module

public import CFSG.LargeExtraspecial.DWSm77Basic
public import CFSG.LargeExtraspecial.DWRed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

namespace Setting

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

noncomputable abbrev ρL (m : S.M) : S.Qt ≃ₗ[ZMod 2] S.Qt := (S.ρ m : S.O)

theorem ρL_one : S.ρL 1 = 1 := by
  show ((S.ρ 1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1
  rw [map_one, Subgroup.coe_one]

theorem ρL_mul (m n : S.M) : S.ρL (m * n) = S.ρL m * S.ρL n := by
  show ((S.ρ (m * n) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((S.ρ n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  rw [map_mul, Subgroup.coe_mul]

theorem ρL_cl (m : S.M) {x : G} (hx : x ∈ S.QG) :
    S.ρL m (S.cl x) = S.cl ((m : G) * x * (m : G)⁻¹) := S.ρ_cl m hx

theorem ρL_inv_apply_apply (m : S.M) (v : S.Qt) : S.ρL m⁻¹ (S.ρL m v) = v :=
  DW.ρ_inv_apply_apply m v

theorem ρL_apply_apply_inv (m : S.M) (v : S.Qt) : S.ρL m (S.ρL m⁻¹ v) = v := by
  apply (S.ρL m⁻¹).injective
  rw [S.ρL_inv_apply_apply]

theorem exists_sq_eq_z_of_lt_card {R : Subgroup G} (hRQ : R ≤ S.QG)
    (hR : 2 ^ (S.width + 1) < Nat.card R) : ∃ c ∈ R, c * c = S.z := by
  by_contra h
  have hsq : ∀ x ∈ R, x * x = 1 := fun x hx => by
    rcases S.sq_eq_one_or_z (hRQ hx) with h1 | h1
    · simpa [pow_two] using h1
    · exact absurd ⟨x, hx, by simpa [pow_two] using h1⟩ h
  have hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    have h1 : x * y * (y * x) = 1 := by
      calc x * y * (y * x) = x * (y * y) * x := by group
        _ = 1 := by rw [hsq y hy, mul_one, hsq x hx]
    have h2 : (y * x) * (y * x) = 1 := hsq (y * x) (R.mul_mem hy hx)
    have h3 : (y * x)⁻¹ = y * x := inv_eq_of_mul_eq_one_right h2
    calc x * y = (x * y * (y * x)) * (y * x)⁻¹ := by group
      _ = (y * x)⁻¹ := by rw [h1, one_mul]
      _ = y * x := h3
  have hle := S.card_le_of_commute hRQ hcomm
  omega

theorem two_mul_card_centralizer_inf_QG {t : G} (ht : t ∈ S.QG) (ht1 : t ≠ 1) (htz : t ≠ S.z) :
    2 * Nat.card ↥(centralizer ({t} : Set G) ⊓ S.QG) = Nat.card S.QG := by
  have h := Subgroup.relIndex_mul_card (S.QG ⊓ centralizer ({t} : Set G)) S.QG
  rw [S.relIndex_centralizer_eq_two ht ht1 htz,
    inf_eq_left.mpr (inf_le_left : S.QG ⊓ centralizer ({t} : Set G) ≤ S.QG)] at h
  rw [inf_comm]
  exact h

end Setting

end CFSG.LargeExtraspecial

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
variable {G : Type*} [Group G] [Finite G]

structure NormalQuat (S : Setting G) (P : Subgroup G) : Prop where
  le_QG : P ≤ S.QG
  conj_mem : ∀ m ∈ S.M, ∀ p ∈ P, m * p * m⁻¹ ∈ P
  card_eq : Nat.card P = 8
  mul_self_eq : ∀ p ∈ P, p ≠ 1 → p ≠ S.z → p * p = S.z

namespace NormalQuat

variable {S : Setting G} {P : Subgroup G}

theorem z_mem (hP : NormalQuat S P) : S.z ∈ P := by
  have hne : P ≠ ⊥ := by
    intro hbot
    have hc : Nat.card P = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hP.card_eq] at hc
    omega
  obtain ⟨p, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  by_cases hz : (p : G) = S.z
  · exact hz ▸ p.2
  · have h := hP.mul_self_eq (p : G) p.2 (fun h1 => hp1 (Subtype.ext h1)) hz
    rw [← h]
    exact P.mul_mem p.2 p.2

theorem mul_self_eq_one_iff (hP : NormalQuat S P) {p : G} (hp : p ∈ P) :
    p * p = 1 ↔ p = 1 ∨ p = S.z := by
  constructor
  · intro h
    by_cases h1 : p = 1
    · exact Or.inl h1
    · by_cases hz : p = S.z
      · exact Or.inr hz
      · rw [hP.mul_self_eq p hp h1 hz] at h
        exact absurd h S.z_ne_one
  · rintro (rfl | rfl)
    · simp
    · exact S.z_mul_z

theorem z_mem_of_ne_bot (hP : NormalQuat S P) {H : Subgroup G} (hHP : H ≤ P) (hH : H ≠ ⊥) :
    S.z ∈ H := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  by_cases hxz : (x : G) = S.z
  · exact hxz ▸ x.2
  · have h := hP.mul_self_eq (x : G) (hHP x.2) (fun h1 => hx1 (Subtype.ext h1)) hxz
    rw [← h]
    exact H.mul_mem x.2 x.2

theorem conj (hP : NormalQuat S P) (g : G) :
    NormalQuat (S.conjBy g) (P.map (MulAut.conj g).toMonoidHom) where
  le_QG := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [show (S.conjBy g).QG = S.Qa g from rfl, S.Qa_eq_map]
    exact Subgroup.mem_map_of_mem _ (hP.le_QG hp)
  conj_mem := by
    rintro m hm p' hp'
    obtain ⟨p, hp, rfl⟩ := hp'
    rw [Sm77.mem_conjBy_M_iff S] at hm
    refine ⟨(g⁻¹ * m * g) * p * (g⁻¹ * m * g)⁻¹, hP.conj_mem _ hm p hp, ?_⟩
    simp
    group
  card_eq := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card_eq]
  mul_self_eq := by
    rintro p' hp' hp'1 hp'z
    obtain ⟨p, hp, rfl⟩ := hp'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Setting.conjBy_z] at hp'1 hp'z ⊢
    have hp1 : p ≠ 1 := by intro h; exact hp'1 (by rw [h]; group)
    have hpz : p ≠ S.z := by intro h; exact hp'z (by rw [h])
    calc (g * p * g⁻¹) * (g * p * g⁻¹) = g * (p * p) * g⁻¹ := by group
      _ = g * S.z * g⁻¹ := by rw [hP.mul_self_eq p hp hp1 hpz]

theorem card_clSub (hP : NormalQuat S P) : Nat.card (S.clSub P) = 4 := by
  have hpre : S.clPre (S.clSub P) = P := S.clPre_clSub hP.le_QG hP.z_mem
  have h := S.card_clPre (S.clSub P)
  rw [hpre, hP.card_eq] at h
  omega

theorem finrank_clSub (hP : NormalQuat S P) : finrank (ZMod 2) (S.clSub P) = 2 := by
  have h := S.card_submodule (S.clSub P)
  rw [hP.card_clSub] at h
  have h4 : (2 : ℕ) ^ finrank (ZMod 2) (S.clSub P) = 2 ^ 2 := by rw [← h]; norm_num
  exact Nat.pow_right_injective le_rfl h4

theorem q_eq_one_of_mem_clSub (hP : NormalQuat S P) {v : S.Qt} (hv : v ∈ S.clSub P)
    (hv0 : v ≠ 0) : S.q v = 1 := by
  obtain ⟨p, hp, hpQ, rfl⟩ := S.mem_clSub_iff.mp hv
  have hp1 : p ≠ 1 := fun h => hv0 (by rw [h, S.cl_one])
  have hpz : p ≠ S.z := fun h => hv0 (by rw [h, S.cl_z])
  have hp2 : p ^ 2 ≠ 1 := by
    rw [pow_two, hP.mul_self_eq p hp hp1 hpz]
    exact S.z_ne_one
  exact (S.q_cl_eq_one_iff hpQ).mpr hp2

theorem isMbarInvariant_clSub (hP : NormalQuat S P) : IsMbarInvariant S (S.clSub P) := by
  intro m v hv
  obtain ⟨p, hp, hpQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.ρ_cl m hpQ]
  exact S.cl_mem_clSub (hP.conj_mem m m.2 p hp) (S.conj_mem_QG m.2 hpQ)

theorem isCompl_clSub_perp (hP : NormalQuat S P) :
    IsCompl (S.clSub P) (perp S (S.clSub P)) := by
  rw [perp, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint S.polarBilin_isRefl, disjoint_iff,
    eq_bot_iff]
  intro v hv
  by_contra hv0
  have hspan_le : ZMod 2 ∙ v ≤ S.clSub P :=
    (Submodule.span_singleton_le_iff_mem v (S.clSub P)).mpr hv.1
  have hspan_ne : ZMod 2 ∙ v ≠ S.clSub P := by
    intro heq
    have h1 : finrank (ZMod 2) (ZMod 2 ∙ v) = finrank (ZMod 2) (S.clSub P) := by rw [heq]
    rw [finrank_span_singleton hv0, hP.finrank_clSub] at h1
    omega
  obtain ⟨u, huW, hu_notin⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hspan_le hspan_ne)
  have hu0 : u ≠ 0 := by
    intro h
    apply hu_notin
    rw [h]
    exact Submodule.zero_mem _
  have hvq : S.q v = 1 := hP.q_eq_one_of_mem_clSub hv.1 hv0
  have huq : S.q u = 1 := hP.q_eq_one_of_mem_clSub huW hu0
  have hsum_mem : v + u ∈ S.clSub P := (S.clSub P).add_mem hv.1 huW
  have hsum0 : v + u ≠ 0 := by
    intro h
    apply hu_notin
    have h' : u = -v := eq_neg_of_add_eq_zero_right h
    rw [h']
    exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self v)
  have hsumq : S.q (v + u) = 1 := hP.q_eq_one_of_mem_clSub hsum_mem hsum0
  have hzero : S.q (v + u) = 0 := by
    rcases zmod2_cases (S.q (v + u)) with h | h
    · exact h
    · exfalso
      have hp := mem_perp.mp hv.2 u huW
      rw [polar, add_comm u v, h, hvq, huq] at hp
      revert hp
      decide
  rw [hzero] at hsumq
  revert hsumq
  decide

@[expose] noncomputable def ρW (hP : NormalQuat S P) (m : S.M) : S.clSub P ≃ₗ[ZMod 2] S.clSub P where
  toFun v := ⟨S.ρL m v, hP.isMbarInvariant_clSub m v v.2⟩
  invFun v := ⟨S.ρL m⁻¹ v, hP.isMbarInvariant_clSub m⁻¹ v v.2⟩
  left_inv v := by
    apply Subtype.ext
    exact Setting.ρL_inv_apply_apply S m v
  right_inv v := by
    apply Subtype.ext
    exact Setting.ρL_apply_apply_inv S m v
  map_add' v w := by
    apply Subtype.ext
    show S.ρL m ((v : S.Qt) + (w : S.Qt)) = S.ρL m v + S.ρL m w
    exact map_add _ _ _
  map_smul' c v := by
    apply Subtype.ext
    show S.ρL m (c • (v : S.Qt)) = c • S.ρL m v
    exact map_smul _ _ _

@[expose] noncomputable def ρWhom (hP : NormalQuat S P) : S.M →* (S.clSub P ≃ₗ[ZMod 2] S.clSub P) where
  toFun := hP.ρW
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    apply Subtype.ext
    show S.ρL 1 (v : S.Qt) = (v : S.Qt)
    rw [S.ρL_one]
    rfl
  map_mul' := fun m n => by
    refine LinearEquiv.ext fun v => ?_
    apply Subtype.ext
    show S.ρL (m * n) (v : S.Qt) = S.ρL m (S.ρL n (v : S.Qt))
    rw [S.ρL_mul, LinearEquiv.mul_apply]

theorem ρWhom_coe_apply (hP : NormalQuat S P) (m : S.M) (v : S.clSub P) :
    ((hP.ρWhom m v : S.clSub P) : S.Qt) = S.ρL m (v : S.Qt) := rfl

@[expose] def InnerOn (P : Subgroup G) (m : G) : Prop :=
  ∀ p ∈ P, m * p * m⁻¹ = p ∨ m * p * m⁻¹ = p * S.z

theorem innerOn_iff_ρWhom_eq_one (hP : NormalQuat S P) {m : S.M} :
    InnerOn (S := S) P (m : G) ↔ hP.ρWhom m = 1 := by
  constructor
  · intro h
    refine LinearEquiv.ext fun v => ?_
    apply Subtype.ext
    obtain ⟨p, hp, hpQ, hpv⟩ := S.mem_clSub_iff.mp v.2
    show S.ρL m (v : S.Qt) = (v : S.Qt)
    rw [show (v : S.Qt) = S.cl p from hpv.symm]
    show S.ρL m (S.cl p) = S.cl p
    rw [S.ρL_cl m hpQ]
    rcases h p hp with h' | h'
    · rw [h']
    · rw [h', S.cl_mul_z hpQ]
  · intro h p hp
    have hpQ := hP.le_QG hp
    have hfix : S.ρL m (S.cl p) = S.cl p := by
      have h' := congrArg (fun e : S.clSub P ≃ₗ[ZMod 2] S.clSub P =>
        (e ⟨S.cl p, S.cl_mem_clSub hp hpQ⟩ : S.clSub P)) h
      have h'' := congrArg Subtype.val h'
      simpa [ρWhom_coe_apply] using h''
    rw [S.ρL_cl m hpQ] at hfix
    rcases (S.cl_eq_cl_iff hpQ (S.conj_mem_QG m.2 hpQ)).mp hfix.symm with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'

@[expose] noncomputable def innerPart (hP : NormalQuat S P) (R : Subgroup S.M) : Subgroup S.M :=
  R ⊓ (hP.ρWhom).ker

@[expose] noncomputable def linearEquivToPerm (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    (V ≃ₗ[ZMod 2] V) →* Equiv.Perm {v : V // v ≠ 0} where
  toFun e :=
    { toFun := fun v => ⟨e v, fun h => v.2 (e.injective (by simpa using h))⟩
      invFun := fun v => ⟨e.symm v, fun h => v.2 (e.symm.injective (by simpa using h))⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp
      right_inv := fun v => by
        apply Subtype.ext
        simp }
  map_one' := by
    ext v
    rfl
  map_mul' := fun e f => by
    ext v
    rfl

theorem linearEquivToPerm_injective (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    Function.Injective (linearEquivToPerm V) := by
  intro e f h
  ext v
  by_cases hv : v = 0
  · rw [hv, map_zero, map_zero]
  · have h' := congrArg (fun σ : Equiv.Perm {v : V // v ≠ 0} => (σ ⟨v, hv⟩ : V)) h
    simpa [linearEquivToPerm] using h'

theorem card_perm_nonzero_clSub (hP : NormalQuat S P) :
    Nat.card (Equiv.Perm {v : S.clSub P // v ≠ 0}) = 6 := by
  haveI : Fintype (S.clSub P) := Fintype.ofFinite _
  haveI : Fintype {x : S.clSub P | x ≠ 0} := Fintype.ofFinite _
  have h3 : Nat.card {v : S.clSub P // v ≠ 0} = 3 := by
    have h1 := Set.card_ne_eq (0 : S.clSub P)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hP.card_clSub] at h1
    exact h1
  rw [Nat.card_perm, h3]
  norm_num

theorem card_le_two_mul_card_innerPart (hP : NormalQuat S P) (R : Subgroup S.M) {k : ℕ}
    (hk : Nat.card R = 2 ^ k) : Nat.card R ≤ 2 * Nat.card (hP.innerPart R) := by
  classical
  haveI : Fintype {v : S.clSub P // v ≠ 0} := Fintype.ofFinite _
  set ψ : R →* Equiv.Perm {v : S.clSub P // v ≠ 0} :=
    (linearEquivToPerm (S.clSub P)).comp (hP.ρWhom.comp R.subtype) with hψ
  have hψker : ψ.ker = (hP.innerPart R).subgroupOf R := by
    ext x
    show (linearEquivToPerm (S.clSub P) (hP.ρWhom (x : R)) = 1) ↔
      x ∈ (hP.innerPart R).subgroupOf R
    rw [innerPart, Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : hP.ρWhom (x : R) = 1 :=
        linearEquivToPerm_injective _ (by rw [map_one]; exact h)
      exact ⟨x.2, h1⟩
    · rintro ⟨-, h1⟩
      rw [h1, map_one]
  have hcard : Nat.card R = Nat.card (R ⧸ ψ.ker) * Nat.card ψ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have hiso : Nat.card (R ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have hker : Nat.card ψ.ker = Nat.card (hP.innerPart R) := by
    rw [hψker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : hP.innerPart R ≤ R)).toEquiv
  have hdvd6 : Nat.card ψ.range ∣ 6 := by
    have h1 : Nat.card ψ.range ∣
        Nat.card (Equiv.Perm {v : S.clSub P // v ≠ 0}) := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [hP.card_perm_nonzero_clSub] at h1
  have hdvd2 : Nat.card ψ.range ∣ 2 ^ k := by
    rw [← hk, hcard, hiso]
    exact dvd_mul_right _ _
  have hle : Nat.card ψ.range ≤ 2 := by
    obtain ⟨j, hj, hjE⟩ := (Nat.dvd_prime_pow (p := 2) (m := k) Nat.prime_two).mp hdvd2
    have h6 : 2 ^ j ∣ 6 := by rw [← hjE]; exact hdvd6
    have hj2 : j ≤ 2 := by
      by_contra h
      push Not at h
      have h8 : 8 ≤ 2 ^ j := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
      have hle6 : 2 ^ j ≤ 6 := Nat.le_of_dvd (by norm_num) h6
      omega
    interval_cases j
    · rw [hjE]; norm_num
    · rw [hjE]; norm_num
    · exact absurd h6 (by norm_num)
  calc Nat.card R = Nat.card ψ.range * Nat.card ψ.ker := by rw [hcard, hiso]
    _ ≤ 2 * Nat.card ψ.ker := Nat.mul_le_mul_right _ hle
    _ = 2 * Nat.card (hP.innerPart R) := by rw [hker]

theorem conj_mul_self_eq_of_innerOn (hP : NormalQuat S P) {m : G} (hm : m ∈ S.M)
    (h : InnerOn (S := S) P m) {p : G} (hp : p ∈ P) :
    (m * m) * p * (m * m)⁻¹ = p := by
  have hz : m * S.z * m⁻¹ = S.z := by rw [S.z_comm hm]; group
  rcases h p hp with h' | h'
  · have h1 : (m * m) * p * (m * m)⁻¹ = m * (m * p * m⁻¹) * m⁻¹ := by group
    rw [h1, h']
    exact h'
  · have h1 : (m * m) * p * (m * m)⁻¹ = m * (m * p * m⁻¹) * m⁻¹ := by group
    rw [h1, h']
    have h2 : m * (p * S.z) * m⁻¹ = (m * p * m⁻¹) * (m * S.z * m⁻¹) := by group
    rw [h2, h', hz, mul_assoc, S.z_mul_z, mul_one]

end NormalQuat

end CFSG.LargeExtraspecial.DW

