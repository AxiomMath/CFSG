module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413L34b
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Seven
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub1

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem card_le_16 (hL : LLayer hs π) {P : Subgroup PSL3Four.R}
    (hP : IsPGroup 2 P)
    (hPle : P ≤ ((PSL3Four.S.subgroupOf PSL3Four.R) ⊔ zpowers (hL.rho (hs.setup.tBar i j))) ⊓
      centralizer {hL.rho (hs.setup.tBar i j)}) : Nat.card P ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set rt := hL.rho (hs.setup.tBar i j) with hrt
  set S' := PSL3Four.S.subgroupOf PSL3Four.R with hS'
  obtain ⟨hrt2, hrtS⟩ := hL.rho_t_facts
  have hrt2' : rt ^ 2 = 1 := by rw [← hrt2]; exact pow_orderOf_eq_one rt
  have hn : ∀ k ∈ S', rt * k * rt⁻¹ ∈ S' := fun k hk => PSL3Four.conj_mem_S rt.2 hk
  have hu2 : rt ^ 2 ∈ S' := by rw [hrt2']; exact one_mem _
  have h8 : Nat.card ↥(S' ⊓ P) ≤ 8 := by
    have hle : (S' ⊓ P).map PSL3Four.R.subtype ≤
        centralizer {(rt : Equiv.Perm (Fin 42))} ⊓ PSL3Four.S := by
      rintro _ ⟨y, hy, rfl⟩
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, (mem_inf.mp hy).1⟩
      have := mem_centralizer_singleton_iff.mp (mem_inf.mp (hPle (mem_inf.mp hy).2)).2
      exact congrArg Subtype.val this
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (subtype_injective _), hL.card_centralizer_rho_t] at hdvd
    have h2 : IsPGroup 2 ↥(S' ⊓ P) := hP.to_le inf_le_right
    have := HarrisEnd.card_le_twoPart_of_dvd h2 (by norm_num) hdvd
    rwa [show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)] at this
  have hrel : S'.relIndex P ≤ 2 := by
    have h1 : S'.relIndex (S' ⊔ zpowers rt) = 2 := by
      have hc := card_sup_zpowers hn hu2 (fun h => hrtS h)
      have h2 := Subgroup.relIndex_mul_card S' (S' ⊔ zpowers rt)
      rw [inf_of_le_left le_sup_left, hc] at h2
      have hpos : 0 < Nat.card ↥S' := Nat.card_pos
      nlinarith
    calc S'.relIndex P ≤ S'.relIndex (S' ⊔ zpowers rt) :=
          Subgroup.relIndex_le_of_le_right (hPle.trans inf_le_left) (by rw [h1]; norm_num)
      _ = 2 := h1
  have h := Subgroup.relIndex_mul_card S' P
  rw [← h]
  calc S'.relIndex P * Nat.card ↥(S' ⊓ P) ≤ 2 * 8 := Nat.mul_le_mul hrel h8
    _ = 16 := by norm_num

theorem exists_x (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥) :
    ∃ x ∈ S ⊓ L, x ^ 2 = 1 ∧
      ∃ hxM : x ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X),
        ((hL.rho (QuotientGroup.mk ⟨x, hxM⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) ∉ PSL3Four.S ∧
        ((hL.rho (QuotientGroup.mk ⟨x, hxM⟩ * hs.setup.tBar i j) : PSL3Four.R) :
          Equiv.Perm (Fin 42)) ∉ PSL3Four.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨e⟩⟩ := hL.seven hZ
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set πM := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπM
  set rt := hL.rho (hs.setup.tBar i j) with hrt
  set S' := PSL3Four.S.subgroupOf PSL3Four.R with hS'
  set Rt := S' ⊔ zpowers rt with hRt
  obtain ⟨hrt2, hrtS⟩ := hL.rho_t_facts
  have hrt2' : rt ^ 2 = 1 := by rw [← hrt2]; exact pow_orderOf_eq_one rt
  have hn : ∀ k ∈ S', rt * k * rt⁻¹ ∈ S' := fun k hk => PSL3Four.conj_mem_S rt.2 hk
  have hu2 : rt ^ 2 ∈ S' := by rw [hrt2']; exact one_mem _
  have hrtinv : rt⁻¹ = rt := inv_eq_of_mul_eq_one_right (by rw [← sq, hrt2'])
  have hDM : S ⊓ L ≤ M := hs.setup.D_le_centralizer_beta i j
  set K₂ := (Rt.comap (hL.rho.comp πM)).map M.subtype with hK₂
  have hmemK₂ : ∀ (x : X) (hx : x ∈ M), x ∈ K₂ ↔ hL.rho (πM ⟨x, hx⟩) ∈ Rt := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  by_contra hcon
  have hgood : ∀ x ∈ S ⊓ L, x ^ 2 = 1 → x ∈ K₂ := by
    intro x hxD hx2
    rw [hmemK₂ x (hDM hxD)]
    by_contra hnot
    apply hcon
    refine ⟨x, hxD, hx2, hDM hxD, fun h => hnot (mem_sup_left (Subgroup.mem_subgroupOf.mpr h)),
      fun h => hnot ?_⟩
    have h' : hL.rho (πM ⟨x, hDM hxD⟩) * rt ∈ S' := by
      rw [Subgroup.mem_subgroupOf, hrt, ← map_mul]
      exact h
    rw [show hL.rho (πM ⟨x, hDM hxD⟩) = (hL.rho (πM ⟨x, hDM hxD⟩) * rt) * rt⁻¹ by group]
    exact mul_mem (mem_sup_left h') (mem_sup_right (inv_mem (mem_zpowers _)))
  have hDK : S ⊓ L ≤ K₂ := by
    intro d hd
    have hd' : (⟨d, hd⟩ : ↥(S ⊓ L)) ∈ ((closure {DihedralGroup.sr (0 : ZMod (2 ^ 3)),
        DihedralGroup.sr 1}).map e.symm.toMonoidHom) := by
      rw [HarrisEnd.closure_sr_eq_top]
      exact ⟨e ⟨d, hd⟩, mem_top _, by simp⟩
    rw [MonoidHom.map_closure] at hd'
    have hcl : closure ((e.symm.toMonoidHom) '' {DihedralGroup.sr (0 : ZMod (2 ^ 3)),
        DihedralGroup.sr 1}) ≤ K₂.comap (S ⊓ L).subtype := by
      rw [closure_le]
      rintro _ ⟨g, hg, rfl⟩
      have hg2 : ((e.symm.toMonoidHom g : ↥(S ⊓ L)) : X) ^ 2 = 1 := by
        rcases hg with rfl | rfl <;>
        · rw [← Subgroup.coe_pow, ← map_pow, sq, DihedralGroup.sr_mul_self, map_one,
            Subgroup.coe_one]
      exact hgood _ (e.symm.toMonoidHom g).2 hg2
    exact hcl hd'
  have htK : t ∈ K₂ := by
    rw [hmemK₂ t (hs.setup.t_mem_centralizer_beta i j)]
    exact mem_sup_right (mem_zpowers _)
  have hβK : β ∈ K₂ := by
    rw [hmemK₂ β (mem_centralizer_singleton_iff.mpr rfl)]
    have : hL.rho (πM ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩) = 1 :=
      (hL.rho_eq_one_iff _).mpr hs.betaBar_mem_pCore
    rw [this]
    exact one_mem _
  have hzK : z ∈ K₂ := hDK hs.lemma45.z_mem.1
  have hwK : w ∈ K₂ := by
    have h1 : w ^ (orderOf w / 2) = β * (t ^ i * z ^ j)⁻¹ := by
      rw [hβ, mul_assoc _ (t ^ i), mul_inv_cancel_right]
    rw [hL.orderOf_w hZ, show (2 : ℕ) / 2 = 1 from rfl, pow_one] at h1
    rw [h1]
    exact mul_mem hβK (inv_mem (mul_mem (pow_mem htK _) (pow_mem hzK _)))
  have hTK : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ K₂ :=
    sup_le (sup_le (zpowers_le.mpr htK) hDK) (zpowers_le.mpr hwK)
  have hT1 : IsSylowOf 2 (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (centralizer ({t} : Set X) ⊓ M) :=
    hs.lemma45.isSylowOf_T
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  have hTM : T ≤ M := hT1.le.trans inf_le_right
  have hTH : T ≤ centralizer ({t} : Set X) := hT1.le.trans inf_le_left
  set Tb := (T.subgroupOf M).map πM with hTb
  have hTp : IsPGroup 2 (T.subgroupOf M) :=
    hT1.isPGroup.of_equiv (subgroupOfEquivOfLe hTM).symm
  have hcardT : Nat.card Tb = Nat.card T := by
    rw [hTb, GSThmB.OddQuot.card_map_of_isPGroup hTp,
      Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv]
  have hTbC : Tb ≤ centralizer {hs.setup.tBar i j} := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hgt : g * ⟨t, hs.setup.t_mem_centralizer_beta i j⟩ =
        ⟨t, hs.setup.t_mem_centralizer_beta i j⟩ * g :=
      Subtype.ext (mem_centralizer_singleton_iff.mp (hTH hg))
    change πM g * πM ⟨t, _⟩ = πM ⟨t, _⟩ * πM g
    rw [← map_mul, ← map_mul, hgt]
  set φ : ↥Tb →* PSL3Four.R := hL.rho.comp Tb.subtype with hφ
  have hker : Nat.card φ.ker ≤ 2 := by
    have hle : φ.ker.map Tb.subtype ≤ zpowers (betaBar β) := by
      rintro _ ⟨g, hg, rfl⟩
      replace hg := MonoidHom.mem_ker.mp hg
      have h1 : (g : MBar β) ∈ pCore 2 (MBar β) ⊓ centralizer {hs.setup.tBar i j} :=
        ⟨(hL.rho_eq_one_iff g).mp hg, hTbC g.2⟩
      rw [hL.h412.pCore_inf_centralizer] at h1
      exact h1
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (subtype_injective _), Nat.card_zpowers] at h1
    have h2 : orderOf (betaBar β) ∣ 2 := orderOf_dvd_of_pow_eq_one hs.betaBar_sq
    exact h1.trans (Nat.le_of_dvd (by norm_num) h2)
  have hrange : Nat.card φ.range ≤ 16 := by
    have hTbp : IsPGroup 2 Tb := hTp.map πM
    refine hL.card_le_16 (hTbp.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective) ?_
    rintro _ ⟨g, rfl⟩
    refine mem_inf.mpr ⟨?_, ?_⟩
    · obtain ⟨g', hg', hg'eq⟩ := g.2
      change hL.rho (g : MBar β) ∈ Rt
      rw [← hg'eq]
      exact (hmemK₂ g' g'.2).mp (hTK (Subgroup.mem_subgroupOf.mp hg'))
    · rw [mem_centralizer_singleton_iff]
      have hgt : (g : MBar β) * hs.setup.tBar i j = hs.setup.tBar i j * g :=
        mem_centralizer_singleton_iff.mp (hTbC g.2)
      change hL.rho g * hL.rho (hs.setup.tBar i j) = hL.rho (hs.setup.tBar i j) * hL.rho g
      rw [← map_mul, ← map_mul, hgt]
  have h64 := hL.card_T hZ
  rw [← hT, ← hcardT, ← Subgroup.card_ker_mul_card_range φ] at h64
  have := Nat.mul_le_mul hker hrange
  omega

theorem graph_unitary
    (hL : LLayer hs π) {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg2 : g ^ 2 = 1)
    (hgt : g * hs.setup.tBar i j = hs.setup.tBar i j * g)
    (h0 : (hL.rho g : Equiv.Perm (Fin 42)) ∉ PSL3Four.S)
    (h1 : (hL.rho (g * hs.setup.tBar i j) : Equiv.Perm (Fin 42)) ∉ PSL3Four.S) :
    ((∃ c ∈ PSL3Four.R, (hL.rho g : Equiv.Perm (Fin 42)) = c * PSL3Four.r₃ * c⁻¹) ∧
        ∃ c ∈ PSL3Four.R, (hL.rho (g * hs.setup.tBar i j) : Equiv.Perm (Fin 42)) =
          c * PSL3Four.r₄ * c⁻¹) ∨
      ((∃ c ∈ PSL3Four.R, (hL.rho g : Equiv.Perm (Fin 42)) = c * PSL3Four.r₄ * c⁻¹) ∧
        ∃ c ∈ PSL3Four.R, (hL.rho (g * hs.setup.tBar i j) : Equiv.Perm (Fin 42)) =
          c * PSL3Four.r₃ * c⁻¹) := by
  obtain ⟨c, hc, hrc⟩ := hL.rho_t_conj
  obtain ⟨hrt2, -⟩ := hL.rho_t_facts
  rw [map_mul, Subgroup.coe_mul]
  rw [map_mul, Subgroup.coe_mul] at h1
  set r : Equiv.Perm (Fin 42) := ((hL.rho (hs.setup.tBar i j) : PSL3Four.R) :
    Equiv.Perm (Fin 42)) with hr
  set s : Equiv.Perm (Fin 42) := ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) with hsdef
  have hsR : s ∈ PSL3Four.R := (hL.rho g).2
  have hrR : r ∈ PSL3Four.R := (hL.rho _).2
  have hs2 : s * s = 1 := by
    have h : hL.rho g ^ 2 = 1 := by rw [← map_pow, hg2, map_one]
    rw [pow_two] at h
    exact congrArg Subtype.val h
  have hr2' : r * r = 1 := by
    have h : hL.rho (hs.setup.tBar i j) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (hL.rho (hs.setup.tBar i j))
      rwa [hrt2] at this
    rw [pow_two] at h
    exact congrArg Subtype.val h
  have hsr : s * r = r * s := by
    have h : hL.rho g * hL.rho (hs.setup.tBar i j) = hL.rho (hs.setup.tBar i j) * hL.rho g := by
      rw [← map_mul, ← map_mul, hgt]
    exact congrArg Subtype.val h
  set s₀ := c⁻¹ * s * c with hs₀
  have hs₀R : s₀ ∈ PSL3Four.R := mul_mem (mul_mem (inv_mem hc) hsR) hc
  have hs₀2 : s₀ * s₀ = 1 := by
    rw [hs₀, show c⁻¹ * s * c * (c⁻¹ * s * c) = c⁻¹ * (s * s) * c by group, hs2]
    group
  have hg₅ : PSL3Four.r₂ = c⁻¹ * r * c := by rw [hrc]; group
  have hs₀c : s₀ * PSL3Four.g₅ = PSL3Four.g₅ * s₀ := by
    change s₀ * PSL3Four.r₂ = PSL3Four.r₂ * s₀
    rw [hg₅, hs₀, show c⁻¹ * s * c * (c⁻¹ * r * c) = c⁻¹ * (s * r) * c by group, hsr]
    group
  have hs₀S : s₀ ∉ PSL3Four.S := fun h => h0 (by
    have := PSL3Four.conj_mem_S hc h
    rwa [hs₀, show c * (c⁻¹ * s * c) * c⁻¹ = s by group] at this)
  have hs₀g : PSL3Four.g₅⁻¹ * s₀ ∉ PSL3Four.S := by
    intro h
    apply h1
    have h1' := PSL3Four.conj_mem_S hc h
    have h2 : c * (PSL3Four.g₅⁻¹ * s₀) * c⁻¹ = r⁻¹ * s := by
      change c * (PSL3Four.r₂⁻¹ * s₀) * c⁻¹ = _
      rw [hg₅, hs₀]
      group
    rw [h2] at h1'
    have h3 := PSL3Four.conj_mem_S hrR h1'
    have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2'
    rwa [show r * (r⁻¹ * s) * r⁻¹ = s * r by rw [hri, ← mul_assoc, hr2', one_mul]] at h3
  have hσv : ∀ (ri y : Equiv.Perm (Fin 42)), y * ri * y⁻¹ = s₀ →
      s = (c * y) * ri * (c * y)⁻¹ := by
    intro ri y hy
    rw [show (c * y) * ri * (c * y)⁻¹ = c * (y * ri * y⁻¹) * c⁻¹ by group, hy, hs₀]
    group
  have hστv : ∀ (ri y : Equiv.Perm (Fin 42)), y * ri * y⁻¹ = s₀ * PSL3Four.g₅ →
      s * r = (c * y) * ri * (c * y)⁻¹ := by
    intro ri y hy
    rw [show (c * y) * ri * (c * y)⁻¹ = c * (y * ri * y⁻¹) * c⁻¹ by group, hy, hs₀, hrc]
    change _ = c * (c⁻¹ * s * c * PSL3Four.r₂) * c⁻¹
    group
  rcases conj_r₃_r₄_of_comm_g₅ hs₀R hs₀2 hs₀c hs₀S hs₀g with
    ⟨⟨y, hy, hy3⟩, ⟨y', hy', hy4⟩⟩ | ⟨⟨y, hy, hy4⟩, ⟨y', hy', hy3⟩⟩
  · exact Or.inl ⟨⟨c * y, mul_mem hc (PSL3Four.S_le_R hy), hσv _ _ hy3⟩,
      ⟨c * y', mul_mem hc (PSL3Four.S_le_R hy'), hστv _ _ hy4⟩⟩
  · exact Or.inr ⟨⟨c * y, mul_mem hc (PSL3Four.S_le_R hy), hσv _ _ hy4⟩,
      ⟨c * y', mul_mem hc (PSL3Four.S_le_R hy'), hστv _ _ hy3⟩⟩

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
