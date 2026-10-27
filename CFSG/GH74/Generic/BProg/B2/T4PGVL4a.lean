module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicQuot
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
public import CFSG.GH74.Generic.ClassicalCerts
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74.Generic CFSG.Assembly.LowTwoRank Subgroup

section Odd

variable (L : Type) [Group L]

@[expose] noncomputable def oddCenter : Subgroup L :=
  (pPrimeCore 2 ↥(center L)).map (center L).subtype

variable {L}

theorem oddCenter_le_center : oddCenter L ≤ center L := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem normal_of_le_center {N : Subgroup L} (h : N ≤ center L) : N.Normal :=
  ⟨fun n hn g => by
    have hc := Subgroup.mem_center_iff.1 (h hn) g
    rw [hc, mul_inv_cancel_right]
    exact hn⟩

instance oddCenter_normal : (oddCenter L).Normal := normal_of_le_center oddCenter_le_center

theorem odd_card_oddCenter [Finite L] : Odd (Nat.card ↥(oddCenter L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(oddCenter L) = Nat.card ↥(pPrimeCore 2 ↥(center L)) :=
    Subgroup.card_map_of_injective (center L).subtype_injective
  rw [h1]
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

theorem isPGroup_center_quot [Finite L] (hq : IsQuasisimple L) :
    IsPGroup 2 ↥(center (L ⧸ oddCenter L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hcen⟩ :=
    CFSG.LocalCores.quasisimple_central_quotient hq (oddCenter L) oddCenter_le_center
  rintro ⟨y, hy⟩
  rw [hcen] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hnil : Group.IsNilpotent ↥(center L) := inferInstance
  have htop := CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (Q := ↥(center L)) (p := 2) hnil
  have hn : (pPrimeCore 2 ↥(center L)).Normal := pPrimeCore_normal
  have hmem : (⟨z, hz⟩ : ↥(center L)) ∈
      ((pCore 2 ↥(center L) ⊔ pPrimeCore 2 ↥(center L) : Subgroup ↥(center L)) :
        Set ↥(center L)) := htop (Subgroup.mem_top _)
  rw [Subgroup.mul_normal] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  obtain ⟨k, hk⟩ := (pCore_isPGroup (G := ↥(center L)) (p := 2)) ⟨a, ha⟩
  have hak' : a ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hak : (a : L) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hak'
    simpa using this
  refine ⟨k, Subtype.ext ?_⟩
  have hbO : ((b : L) ^ (2 ^ k)) ∈ oddCenter L :=
    ⟨b ^ (2 ^ k), Subgroup.pow_mem _ hb _, by simp⟩
  have hzab : z = (a : L) * b := (congrArg Subtype.val hab).symm
  have hcomm : Commute (a : L) (b : L) := Subgroup.mem_center_iff.1 b.2 a
  show (QuotientGroup.mk' (oddCenter L) z) ^ (2 ^ k) = 1
  rw [← map_pow, hzab, hcomm.mul_pow, hak, one_mul, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact hbO

end Odd

section Quot

variable {L : Type} [Group L]

theorem mem_centralizer_of_mk {O : Subgroup L} [O.Normal] (hO : O ≤ center L)
    (hodd : Odd (Nat.card ↥O)) {u x : L} (hu : u * u = 1)
    (hx : (QuotientGroup.mk x : L ⧸ O) ∈
      centralizer ({(QuotientGroup.mk u : L ⧸ O)} : Set (L ⧸ O))) :
    x ∈ centralizer ({u} : Set L) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  set c := (x * u)⁻¹ * (u * x) with hc
  have hcO : c ∈ O :=
    QuotientGroup.eq.1 (show (QuotientGroup.mk (x * u) : L ⧸ O) = QuotientGroup.mk (u * x) from
      hx)
  have hcu : u * c = c * u := Subgroup.mem_center_iff.1 (hO hcO) u
  have h1 : x⁻¹ * u * x = u * c := by rw [hc]; group
  have h2 : (u * c) * (u * c) = 1 := by
    rw [← h1]
    calc x⁻¹ * u * x * (x⁻¹ * u * x) = x⁻¹ * (u * u) * x := by group
      _ = 1 := by rw [hu]; group
  have h3 : c * c = 1 := by
    have e : u * c * (u * c) = c * c := by
      calc u * c * (u * c) = u * (c * u) * c := by group
        _ = u * (u * c) * c := by rw [← hcu]
        _ = (u * u) * (c * c) := by group
        _ = c * c := by rw [hu, one_mul]
    rw [← e, h2]
  have hc1 : c = 1 := by
    have hdvd1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h3)
    have hdvd2 : orderOf c ∣ Nat.card ↥O := Subgroup.orderOf_dvd_natCard O hcO
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left hdvd1 (Nat.coprime_two_left.2 hodd)) hdvd2)
  have h4 : u * x = x * u * c := by rw [hc]; group
  rw [hc1, mul_one] at h4
  exact h4.symm

theorem mul_mul_self_eq_one {u₁ u₂ : L} (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1)
    (h₁₂ : u₁ * u₂ = u₂ * u₁) : (u₁ * u₂) * (u₁ * u₂) = 1 := by
  calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
    _ = u₁ * (u₁ * u₂) * u₂ := by rw [h₁₂]
    _ = (u₁ * u₁) * (u₂ * u₂) := by group
    _ = 1 := by rw [h₁, h₂, one_mul]

theorem sup_centralizer_eq_top_of_quot (hperf : commutator L = ⊤) {O : Subgroup L} [O.Normal]
    (hO : O ≤ center L) (hodd : Odd (Nat.card ↥O)) {u₁ u₂ : L} (h₁ : u₁ * u₁ = 1)
    (h₂ : u₂ * u₂ = 1) (h₁₂ : u₁ * u₂ = u₂ * u₁)
    (h : centralizer ({(QuotientGroup.mk u₁ : L ⧸ O)} : Set (L ⧸ O)) ⊔
        centralizer ({(QuotientGroup.mk u₂ : L ⧸ O)} : Set (L ⧸ O)) ⊔
        centralizer ({(QuotientGroup.mk (u₁ * u₂) : L ⧸ O)} : Set (L ⧸ O)) = ⊤) :
    centralizer ({u₁} : Set L) ⊔ centralizer ({u₂} : Set L) ⊔
      centralizer ({u₁ * u₂} : Set L) = ⊤ := by
  set Γ := centralizer ({u₁} : Set L) ⊔ centralizer ({u₂} : Set L) ⊔
    centralizer ({u₁ * u₂} : Set L) with hΓ
  have hC : ∀ u : L, u * u = 1 → centralizer ({u} : Set L) ≤ Γ →
      centralizer ({(QuotientGroup.mk u : L ⧸ O)} : Set (L ⧸ O)) ≤ Γ.map (QuotientGroup.mk' O) := by
    intro u hu hle y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨x, hle (mem_centralizer_of_mk hO hodd hu hy), rfl⟩
  have hmap : Γ.map (QuotientGroup.mk' O) = ⊤ := by
    rw [eq_top_iff, ← h]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hC u₁ h₁ (le_sup_left.trans le_sup_left)
    · exact hC u₂ h₂ (le_sup_right.trans le_sup_left)
    · exact hC (u₁ * u₂) (mul_mul_self_eq_one h₁ h₂ h₁₂) le_sup_right
  have hsurj : ∀ g : L, ∃ γ ∈ Γ, ∃ z ∈ O, g = γ * z := by
    intro g
    have hg : QuotientGroup.mk' O g ∈ Γ.map (QuotientGroup.mk' O) := by
      rw [hmap]; trivial
    obtain ⟨γ, hγ, hγg⟩ := hg
    exact ⟨γ, hγ, γ⁻¹ * g, QuotientGroup.eq.1 hγg, by group⟩
  have hcomm : commutator L ≤ Γ := by
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    obtain ⟨γ₁, hγ₁, z₁, hz₁, rfl⟩ := hsurj g₁
    obtain ⟨γ₂, hγ₂, z₂, hz₂, rfl⟩ := hsurj g₂
    change (γ₁ * z₁) * (γ₂ * z₂) * (γ₁ * z₁)⁻¹ * (γ₂ * z₂)⁻¹ ∈ Γ
    rw [GenLocBasic.comm_central_mul γ₁ γ₂ z₁ z₂ (hO hz₁) (hO hz₂)]
    exact mul_mem (mul_mem (mul_mem hγ₁ hγ₂) (inv_mem hγ₁)) (inv_mem hγ₂)
  rw [hperf] at hcomm
  exact top_le_iff.1 hcomm

end Quot

section Cover

variable {F : Type} [Field F] {H : Subgroup (GL (Fin 4) F)} {K : Type} [Group K]

theorem exists_scalar_of_mem_ker (e : K ⧸ center K ≃* StatedProj H) (π : ↥H →* K)
    (hcompat : ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g) {g : ↥H} (hg : π g = 1) :
    ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c = (g : GL (Fin 4) F) :=
  (cover_central_iff e π hcompat g).1 (by rw [hg]; exact Subgroup.one_mem _)

theorem ker_le_center_of_cover (e : K ⧸ center K ≃* StatedProj H) (π : ↥H →* K)
    (hcompat : ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g) : π.ker ≤ center ↥H := by
  intro g hg
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_ker e π hcompat hg
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ center (GL (Fin 4) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
  exact Subgroup.mem_center_iff.1 hz (h : GL (Fin 4) F)

theorem isPGroup_ker_of_scalar (π : ↥H →* K)
    (hsc : ∀ g ∈ π.ker, ∃ c : Fˣ, c ^ 4 = 1 ∧
      Matrix.GeneralLinearGroup.scalar (Fin 4) c = (g : GL (Fin 4) F)) :
    IsPGroup 2 ↥π.ker := by
  rintro ⟨g, hg⟩
  obtain ⟨c, hc4, hc⟩ := hsc g hg
  refine ⟨2, Subtype.ext (Subtype.ext ?_)⟩
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hc, ← map_pow, show 2 ^ 2 = 4 by norm_num, hc4, map_one]

theorem isPGroup_ker_of_cover_sl (e : K ⧸ center K ≃* StatedProj (StatedSL 4 F))
    (π : ↥(StatedSL 4 F) →* K)
    (hcompat : ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g) : IsPGroup 2 ↥π.ker := by
  refine isPGroup_ker_of_scalar π fun g hg => ?_
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_ker e π hcompat hg
  have hcS : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSL 4 F := by rw [hc]; exact g.2
  exact ⟨c, pow_four_eq_one_of_scalar_mem_statedSL c hcS, hc⟩

theorem isPGroup_ker_of_cover_su {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = (p ^ f) ^ 2)
    (e : K ⧸ center K ≃* StatedProj (StatedSU 4 (p ^ f) F)) (π : ↥(StatedSU 4 (p ^ f) F) →* K)
    (hcompat : ∀ g, e (QuotientGroup.mk (π g)) = QuotientGroup.mk g) : IsPGroup 2 ↥π.ker := by
  refine isPGroup_ker_of_scalar π fun g hg => ?_
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_ker e π hcompat hg
  have hcS : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSU 4 (p ^ f) F := by
    rw [hc]; exact g.2
  exact ⟨c, ((CFSG.LinearGroups.scalar_mem_statedSU_iff hp hF (by norm_num) c).1 hcS).1, hc⟩

end Cover

end CFSG.GH74.Generic.BProg.B2.T4.PGV
