module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3SixPointA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Props
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Setup

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X5

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {H : Type} [Group H]
  (ρ : H →* (W ≃ₗ[ZMod 2] W)) (L A : Subgroup H) [L.Normal]

theorem card_summand_eq_sixteen (hE : A6SimpleModules) [Finite H]
    (eQ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) (sec : D4Section ρ L A)
    (hcard : Nat.card ↥sec.M ≤ 64)
    (hZ : ∀ z ∈ Subgroup.center ↥L, ∀ m ∈ sec.M, cvAct ρ L (z : H) m = m)
    {U : Submodule (ZMod 2) (W ⧸ fixSub ρ L)} (hU : U ∈ sec.s) : Nat.card ↥U = 16 := by
  classical
  set σ := cvAct ρ L with hσ
  have hsU := sec.ssimple U hU
  have hUinv : Offender.IsInvariant σ L U := hsU.1.1
  have hUM : U ≤ sec.M := by
    rw [← sec.ssup]; exact Finset.le_sup (f := id) hU
  let rU : ↥L →* (↥U ≃ₗ[ZMod 2] ↥U) := resSub σ L U hUinv
  have hZU : Subgroup.center ↥L ≤ rU.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    refine LinearEquiv.ext fun u => Subtype.ext ?_
    show σ (z : H) (u : W ⧸ fixSub ρ L) = u
    exact hZ z hz u (hUM u.2)
  let σU : alternatingGroup (Fin 6) →* (↥U ≃ₗ[ZMod 2] ↥U) :=
    (QuotientGroup.lift (Subgroup.center ↥L) rU hZU).comp eQ.symm.toMonoidHom
  have hσU : ∀ (l : ↥L) (u : ↥U), ((σU (eQ (QuotientGroup.mk l)) u : ↥U) : W ⧸ fixSub ρ L) =
      σ (l : H) u := by
    intro l u
    show ((QuotientGroup.lift (Subgroup.center ↥L) rU hZU (eQ.symm (eQ (QuotientGroup.mk l))) u :
      ↥U) : W ⧸ fixSub ρ L) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hsimp : IsLSimple σU ⊤ (⊤ : Submodule (ZMod 2) ↥U) := by
    refine ⟨fun _ _ _ _ => trivial, ?_, ?_⟩
    · intro h
      apply hsU.1.2.1
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx⟩ : ↥U) ∈ (⊤ : Submodule (ZMod 2) ↥U) := trivial
      rw [h] at h1
      have h2 := (Submodule.mem_bot _).1 h1
      exact (Submodule.mem_bot _).2 (congrArg Subtype.val h2)
    · intro W' hW' _
      have hW''inv : Offender.IsInvariant σ L (W'.map U.subtype) := by
        rintro l hl _ ⟨u, hu, rfl⟩
        refine ⟨σU (eQ (QuotientGroup.mk ⟨l, hl⟩)) u, hW' _ trivial u hu, ?_⟩
        exact hσU ⟨l, hl⟩ u
      have hW''le : W'.map U.subtype ≤ U := by
        rintro _ ⟨u, _, rfl⟩
        exact u.2
      rcases hsU.1.2.2 _ hW''inv hW''le with h | h
      · left
        rw [eq_bot_iff]
        intro u hu
        have h1 : (u : W ⧸ fixSub ρ L) ∈ W'.map U.subtype := ⟨u, hu, rfl⟩
        rw [h] at h1
        have h2 := (Submodule.mem_bot _).1 h1
        exact (Submodule.mem_bot _).2 (Subtype.ext h2)
      · right
        rw [eq_top_iff]
        intro u _
        have h1 : (u : W ⧸ fixSub ρ L) ∈ W'.map U.subtype := by rw [h]; exact u.2
        obtain ⟨w, hw, hwu⟩ := h1
        have h2 : w = u := Subtype.ext hwu
        rw [← h2]
        exact hw
  obtain ⟨hdim, htriv, -⟩ := hE ↥U σU hsimp
  have hcardU : Nat.card ↥U = 2 ^ Module.finrank (ZMod 2) ↥U := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U)
    rwa [Nat.card_zmod] at this
  have hUle : Nat.card ↥U ≤ Nat.card ↥sec.M :=
    Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le hUM)
  rcases hdim with h1 | h4 | h16
  · exfalso
    apply hsU.2
    intro u hu l hl
    have h2 := htriv h1 (eQ (QuotientGroup.mk ⟨l, hl⟩)) ⟨u, hu⟩
    have h3 := hσU ⟨l, hl⟩ ⟨u, hu⟩
    rw [h2] at h3
    exact h3.symm
  · rw [hcardU, h4]; norm_num
  · exfalso
    rw [hcardU, h16] at hUle
    omega

theorem sec_card_eq_sixteen (hE : A6SimpleModules) [Finite H]
    (eQ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) (sec : D4Section ρ L A)
    (hcard : Nat.card ↥sec.M ≤ 64)
    (hZ : ∀ z ∈ Subgroup.center ↥L, ∀ m ∈ sec.M, cvAct ρ L (z : H) m = m) :
    Nat.card ↥sec.M = 16 := by
  classical
  have hne : sec.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply sec.M_ne_bot
    rw [← sec.ssup, h]
    simp
  obtain ⟨U₀, hU₀⟩ := hne
  have h16 := card_summand_eq_sixteen ρ L A hE eQ sec hcard hZ hU₀
  have hall : ∀ U ∈ sec.s, U = U₀ := by
    intro U hU
    by_contra hne
    have h16' := card_summand_eq_sixteen ρ L A hE eQ sec hcard hZ hU
    have hdisj : Disjoint U U₀ := sec.sind.pairwiseDisjoint hU hU₀ hne
    have hsup : U ⊔ U₀ ≤ sec.M := by
      rw [← sec.ssup]
      exact sup_le (Finset.le_sup (f := id) hU) (Finset.le_sup (f := id) hU₀)
    have h1 := natCard_sup_mul_natCard_inf U U₀
    rw [disjoint_iff.1 hdisj] at h1
    have hbot : Nat.card ↥(⊥ : Submodule (ZMod 2) (W ⧸ fixSub ρ L)) = 1 := by simp
    rw [hbot, mul_one, h16, h16'] at h1
    have h2 : Nat.card ↥(U ⊔ U₀) ≤ Nat.card ↥sec.M :=
      Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le hsup)
    omega
  have hM : sec.M = U₀ := by
    rw [← sec.ssup]
    refine le_antisymm (Finset.sup_le fun U hU => (hall U hU).le) (Finset.le_sup (f := id) hU₀)
  rw [hM]; exact h16

omit [Finite W] in
theorem mem_centralizer_of_conj_mod_center [Group.IsPerfect ↥L] {h : H}
    (hc : ∀ l : ↥L, l⁻¹ * conjOn L ⟨h, mem_normalizer_of_normal L h⟩ l ∈ Subgroup.center ↥L) :
    h ∈ Subgroup.centralizer (L : Set H) := by
  have hact : normalizerAct L ⟨h, mem_normalizer_of_normal L h⟩ = 1 := by
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.one_apply, normalizerAct_apply_mk, QuotientGroup.eq]
    have := (Subgroup.center ↥L).inv_mem (hc l)
    simpa using this
  exact mem_centralizer_of_normalizerAct_eq_one L hact

theorem six_point_case_one (hE : A6SimpleModules) [Finite H]
    (hL : CFSG.IsQuasisimple ↥L) (eQ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))
    (hcent : Subgroup.centralizer (L : Set H) = (Subgroup.center ↥L).map L.subtype)
    (sec : D4Section ρ L A) (hcard : Nat.card ↥sec.M ≤ 64)
    (hZ : ∀ z ∈ Subgroup.center ↥L, ∀ m ∈ sec.M, cvAct ρ L (z : H) m = m) :
    ∃ θ : H →* Equiv.Perm (Fin 6), θ.ker = (Subgroup.center ↥L).map L.subtype ∧
      L.map θ = alternatingGroup (Fin 6) := by
  classical
  have hperf : Group.IsPerfect ↥L := hL.1
  have hM16 := sec_card_eq_sixteen ρ L A hE eQ sec hcard hZ
  set M := sec.M with hMdef
  set σ := cvAct ρ L with hσ
  have hfin : Module.finrank (ZMod 2) ↥M = 4 := by
    have h1 : Nat.card ↥M = 2 ^ Module.finrank (ZMod 2) ↥M := by
      have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥M)
      rwa [Nat.card_zmod] at this
    rw [hM16] at h1
    have h2 : (2 : ℕ) ^ 4 = 16 := by norm_num
    exact (Nat.pow_right_injective (le_refl 2) (h1.symm.trans h2.symm))
  have hML : Offender.IsInvariant σ L M := fun l _ => sec.Minv l
  let rL : ↥L →* (↥M ≃ₗ[ZMod 2] ↥M) := resSub σ L M hML
  let rH : H →* (↥M ≃ₗ[ZMod 2] ↥M) := resHom σ M sec.Minv
  have hrHL : ∀ l : ↥L, rH (l : H) = rL l := fun l => rfl
  have hkerL : rL.ker = Subgroup.center ↥L := by
    refine le_antisymm ?_ ?_
    · rcases CFSG.LocalCores.quasisimple_normal_subgroups hL (MonoidHom.normal_ker rL) with
        htop | hle
      · exfalso
        have hfixM : M ≤ fixSub σ L := by
          intro m hm l hl
          have hmem : (⟨l, hl⟩ : ↥L) ∈ rL.ker := by rw [htop]; trivial
          have h1 : rL ⟨l, hl⟩ = 1 := MonoidHom.mem_ker.1 hmem
          have h2 := congrArg (fun f : ↥M ≃ₗ[ZMod 2] ↥M => (f ⟨m, hm⟩ : ↥M).1) h1
          simpa [rL, resSub_apply] using h2
        apply sec.M_ne_bot
        rw [eq_bot_iff]
        intro m hm
        have : m ∈ M ⊓ fixSub σ L := ⟨hm, hfixM hm⟩
        rw [sec.fix_bot] at this
        exact this
      · exact hle
    · intro z hz
      rw [MonoidHom.mem_ker]
      refine LinearEquiv.ext fun m => Subtype.ext ?_
      show σ (z : H) (m : W ⧸ fixSub ρ L) = m
      exact hZ z hz m m.2
  let e1 : (↥L ⧸ Subgroup.center ↥L) ≃* rL.range :=
    (QuotientGroup.quotientMulEquivOfEq hkerL.symm).trans (QuotientGroup.quotientKerEquivRange rL)
  let e2 : rL.range ≃* alternatingGroup (Fin 6) := e1.symm.trans eQ
  obtain ⟨θ', hθ'inj, hθ'im, -⟩ := four_binary_normalizer_six_point hfin rL.range ⟨e2⟩
  have hLconj : ∀ (h : H) (l : ↥L), h * (l : H) * h⁻¹ ∈ L := fun h l =>
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_of_normal L h) l).1 l.2
  have hconj : ∀ (h : H) (l : ↥L), rH h * rL l * (rH h)⁻¹ = rL ⟨h * l * h⁻¹, hLconj h l⟩ := by
    intro h l
    show rH h * rH l * (rH h)⁻¹ = rH (h * l * h⁻¹)
    rw [map_mul, map_mul, map_inv]
  have hnorm : ∀ h : H, rH h ∈ Subgroup.normalizer (rL.range : Set (↥M ≃ₗ[ZMod 2] ↥M)) := by
    intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨_, (hconj h l).symm⟩
    · rintro ⟨l', hl'⟩
      have hl'' : h⁻¹ * (l' : H) * h⁻¹⁻¹ ∈ L := hLconj h⁻¹ l'
      rw [inv_inv] at hl''
      refine ⟨⟨h⁻¹ * l' * h, hl''⟩, ?_⟩
      show rH (h⁻¹ * l' * h) = x
      rw [map_mul, map_mul, map_inv]
      change (rH h)⁻¹ * rL l' * rH h = x
      rw [hl']
      group
  let toN : H →* ↥(Subgroup.normalizer (rL.range : Set (↥M ≃ₗ[ZMod 2] ↥M))) :=
    MonoidHom.codRestrict rH _ hnorm
  let θ : H →* Equiv.Perm (Fin 6) := θ'.comp toN
  have hθ : ∀ h : H, θ h = 1 ↔ rH h = 1 := by
    intro h
    constructor
    · intro h1
      have h2 : toN h = 1 := hθ'inj (by rw [map_one]; exact h1)
      exact congrArg Subtype.val h2
    · intro h1
      have h2 : toN h = 1 := Subtype.ext h1
      show θ' (toN h) = 1
      rw [h2, map_one]
  refine ⟨θ, ?_, ?_⟩
  · ext h
    rw [MonoidHom.mem_ker, hθ]
    constructor
    · intro hh
      have hconj1 : ∀ l : ↥L, l⁻¹ * conjOn L ⟨h, mem_normalizer_of_normal L h⟩ l ∈
          Subgroup.center ↥L := by
        intro l
        rw [← hkerL, MonoidHom.mem_ker, map_mul, map_inv]
        have : rL (conjOn L ⟨h, mem_normalizer_of_normal L h⟩ l) = rL l := by
          show rL ⟨h * l * h⁻¹, hLconj h l⟩ = rL l
          rw [← hconj, hh, one_mul, inv_one, mul_one]
        rw [this, inv_mul_cancel]
      have := mem_centralizer_of_conj_mod_center L hconj1
      rwa [hcent] at this
    · rintro ⟨z, hz, rfl⟩
      have : rL z = 1 := by
        rw [← MonoidHom.mem_ker, hkerL]; exact hz
      exact this
  · rw [← hθ'im]
    ext σ'
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨toN l, ?_, rfl⟩
      show (toN l).1 ∈ rL.range
      exact ⟨⟨l, hl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨l', hl'⟩ := Subgroup.mem_subgroupOf.1 hy
      refine ⟨(l' : H), l'.2, ?_⟩
      show θ' (toN l') = θ' y
      congr 1
      exact Subtype.ext hl'

end CFSG.QuasithinUnique.Setup.X3
