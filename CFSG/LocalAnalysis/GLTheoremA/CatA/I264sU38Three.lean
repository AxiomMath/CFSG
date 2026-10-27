module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264sU38ThreeModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.GroupTheory.PLayer.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.LocalAnalysis.GLTheoremA.U38ThreeModel

section Certs


theorem u38_elemAb_normalizing_two {T A : Subgroup (Equiv.Perm (Fin 513))} (hTX : T ≤ X')
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hAG : A ≤ U38G) (hA : IsElemAbelian 3 A)
    (hAN : A ≤ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 513)))) :
    Nat.card A ≤ 9 ∧ (Nat.card A = 9 → ∃ g ∈ U38G, g⁻¹ * D0 * g ∈ A) := by
  obtain ⟨g, hg, hfix⟩ := exists_conj_fix01 hTX hT2 hT1 hA.isPGroup hAN
  have hA'G : A.map (MulAut.conj g).toMonoidHom ≤ U38G := by
    rintro _ ⟨a, ha, rfl⟩
    exact U38G.mul_mem (U38G.mul_mem hg (hAG ha)) (U38G.inv_mem hg)
  have hA'fix : ∀ e ∈ A.map (MulAut.conj g).toMonoidHom, e 0 = 0 ∧ e 1 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact hfix a ha
  have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨h9, hD⟩ := elemAb_fix01 hA'G hA'fix (hA.map _)
  refine ⟨by rw [← hcard]; exact h9, fun hA9 => ⟨g, hg, ?_⟩⟩
  obtain ⟨a, ha, hga⟩ := hD (hcard.trans hA9)
  have hga' : g * a * g⁻¹ = D0 := hga
  have heq : g⁻¹ * D0 * g = a := by
    rw [← hga']
    group
  rw [heq]
  exact ha

theorem u38_glaPLayer_fix_conj_D0 {g : Equiv.Perm (Fin 513)} (hg : g ∈ U38G) (γ : U38G)
    (hγ : (γ : Equiv.Perm (Fin 513)) = g⁻¹ * D0 * g) :
    GLAPLayer 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (rhoU38 γ)) ≠ ⊥ := by
  have hmap : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (rhoU38 γ)).map X'.subtype =
      Subgroup.centralizer ({(γ : Equiv.Perm (Fin 513))} : Set (Equiv.Perm (Fin 513))) ⊓ X' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : rhoU38 γ y = y := hy
      have h : ((rhoU38 γ y : X') : Equiv.Perm (Fin 513)) = y := congrArg Subtype.val hy'
      rw [rhoU38_apply] at h
      refine Subgroup.mem_inf.2 ⟨?_, y.2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      show (y : Equiv.Perm (Fin 513)) * γ = γ * y
      calc (y : Equiv.Perm (Fin 513)) * γ = (γ * y * (γ : Equiv.Perm (Fin 513))⁻¹) * γ := by rw [h]
        _ = γ * y := by group
    · intro hx
      obtain ⟨hxc, hxX⟩ := Subgroup.mem_inf.1 hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hxc
      refine ⟨⟨x, hxX⟩, ?_, rfl⟩
      show rhoU38 γ ⟨x, hxX⟩ = ⟨x, hxX⟩
      apply Subtype.ext
      rw [rhoU38_apply]
      show (γ : Equiv.Perm (Fin 513)) * x * (γ : Equiv.Perm (Fin 513))⁻¹ = x
      rw [← hxc]
      group
  have hN : g ∈ Subgroup.normalizer (X' : Set (Equiv.Perm (Fin 513))) := U38G_le_normalizer hg
  have hN' : g⁻¹ ∈ Subgroup.normalizer (X' : Set (Equiv.Perm (Fin 513))) :=
    U38G_le_normalizer (U38G.inv_mem hg)
  have hconj : Subgroup.centralizer ({(γ : Equiv.Perm (Fin 513))} : Set (Equiv.Perm (Fin 513))) ⊓ X' =
      (Subgroup.centralizer ({D0} : Set (Equiv.Perm (Fin 513))) ⊓ X').map (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, hγ]
    constructor
    · rintro ⟨hc, hx⟩
      refine ⟨g * x * g⁻¹, Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_normalizer_iff.1 hN x).1 hx⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc g * x * g⁻¹ * D0 = g * (x * (g⁻¹ * D0 * g)) * g⁻¹ := by group
          _ = g * (g⁻¹ * D0 * g * x) * g⁻¹ := by rw [hc]
          _ = D0 * (g * x * g⁻¹) := by group
      · show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
        group
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hc, hyX⟩ := Subgroup.mem_inf.1 hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      have hyc : (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g := by
        show g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g
        rw [inv_inv]
      rw [hyc]
      refine ⟨?_, ?_⟩
      · calc g⁻¹ * y * g * (g⁻¹ * D0 * g) = g⁻¹ * (y * D0) * g := by group
          _ = g⁻¹ * (D0 * y) * g := by rw [hc]
          _ = g⁻¹ * D0 * g * (g⁻¹ * y * g) := by group
      · have h := (Subgroup.mem_normalizer_iff.1 hN' y).1 hyX
        rwa [inv_inv] at h
  intro hbot
  have h1 := glaPLayer_map_eq_of_injective Nat.prime_three X'.subtype X'.subtype_injective
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (rhoU38 γ))
  rw [hbot, Subgroup.map_bot, hmap, hconj,
    ← glaPLayer_map_eq_of_injective Nat.prime_three (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective] at h1
  exact glaPLayer_centralizer_D0
    ((Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) _
      (MulAut.conj g⁻¹).injective).1 h1.symm)

theorem kConcl_u38_three {Y : Type} [Group Y] [Finite Y] {K B : Subgroup Y} (hK : KHyp 3 K B)
    (hc : catalogIs (↥K ⧸ Subgroup.center ↥K) fU38)
    (hcB : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < 3 ^ 3) : KConcl 3 K B := by
  classical
  haveI : K.Normal := hK.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥K := ⟨hK.qs.1⟩
  have hBN : B ≤ Subgroup.normalizer (K : Set Y) := fun b _ =>
    Subgroup.mem_normalizer_iff.2 fun k => ⟨fun hk => hK.normal.conj_mem k hk b, fun hk => by
      simpa [mul_assoc] using hK.normal.conj_mem _ hk b⁻¹⟩
  have hBea : IsElemAbelian 3 B := hK.elem
  have hb3 : ∀ b : ↥B, b ^ 3 = 1 := fun b =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hBea.2 _ b.2)
  have hX : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* ↥(CFSG.PGLModel.projSU 3 2 3)) := by
    obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_u3eight hc
    have hP : CFSG.PGLModel.projImage (CFSG.Open.StatedSU 3 (2 ^ 3) (GaloisField 2 6)) =
        CFSG.PGLModel.projSU 3 2 3 :=
      CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 3 2 3
    exact ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivProjImage _ hP)⟩
  obtain ⟨eX⟩ := nonempty_equiv_X' hX
  let ρ' : U38G ≃* MulAut X' := MulEquiv.ofBijective rhoU38 (rhoU38_bijective hX)
  let ψ : ↥B →* MulAut (↥K ⧸ Subgroup.center ↥K) := normalizerToCenterQuotientAut K B hBN
  let κ : MulAut (↥K ⧸ Subgroup.center ↥K) →* Equiv.Perm (Fin 513) :=
    U38G.subtype.comp (ρ'.symm.toMonoidHom.comp (MulAut.congr eX).toMonoidHom)
  have hκ : Function.Injective κ :=
    U38G.subtype_injective.comp (ρ'.symm.injective.comp (MulAut.congr eX).injective)
  let f : ↥B →* Equiv.Perm (Fin 513) := κ.comp ψ
  have hρf : ∀ b : ↥B, ∃ γ : U38G, (γ : Equiv.Perm (Fin 513)) = f b ∧
      rhoU38 γ = MulAut.congr eX (ψ b) :=
    fun b => ⟨ρ'.symm (MulAut.congr eX (ψ b)), rfl, ρ'.apply_symm_apply (MulAut.congr eX (ψ b))⟩
  have hfC : ∀ b : ↥B, f b = 1 ↔ (b : Y) ∈ B ⊓ Subgroup.centralizer (K : Set Y) := by
    intro b
    rw [← normalizerToCenterQuotientAut_eq_one_iff hperf hBN b]
    exact (injective_iff_map_eq_one' κ).1 hκ (ψ b)
  have hBC : Nat.card B = Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) * Nat.card f.range := by
    have h1 := Subgroup.card_ker_mul_card_range f
    have hmap : f.ker.map B.subtype = B ⊓ Subgroup.centralizer (K : Set Y) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hfC x).1 (MonoidHom.mem_ker.1 hx)
      · intro hy
        exact ⟨⟨y, (Subgroup.mem_inf.1 hy).1⟩, MonoidHom.mem_ker.2 ((hfC _).2 hy), rfl⟩
    have h3 : Nat.card f.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
      rw [← hmap, Subgroup.card_map_of_injective B.subtype_injective]
    rw [← h1, h3]
  have hA : IsElemAbelian 3 f.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨b1, hb1⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨b2, hb2⟩ := MonoidHom.mem_range.1 y.2
      have hcomm : b1 * b2 = b2 * b1 := Subtype.ext (isElemAbelian_commute hBea b1.2 b2.2)
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hb1, ← hb2, ← map_mul, ← map_mul, hcomm]
    · obtain ⟨b1, rfl⟩ := MonoidHom.mem_range.1 hx
      rw [← map_pow, hb3, map_one]
  have hAG : f.range ≤ U38G := by
    rintro _ ⟨b, rfl⟩
    exact (ρ'.symm (MulAut.congr eX (ψ b))).2
  obtain ⟨T, hTK, hT2, hTne, hBT⟩ := hK.twogrp
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  let ι : ↥K →* Equiv.Perm (Fin 513) := X'.subtype.comp (eX.toMonoidHom.comp π)
  have hTK2 : IsPGroup 2 (T.subgroupOf K) := hT2.comap_of_injective K.subtype K.subtype_injective
  have hT0X : (T.subgroupOf K).map ι ≤ X' := by
    rintro _ ⟨t, -, rfl⟩
    exact (eX (π t)).2
  have hT02 : IsPGroup 2 ((T.subgroupOf K).map ι) := hTK2.map ι
  have hZ3 : IsPGroup 3 (Subgroup.center ↥K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.isPGroup_center_of_pPrimeCore_eq_bot Nat.prime_three hK.core
  have hT0ne : (T.subgroupOf K).map ι ≠ ⊥ := by
    obtain ⟨⟨t, htT⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hTne
    intro hbot
    have htK : t ∈ K := hTK htT
    have hι : ι ⟨t, htK⟩ = 1 := by
      have hmem : ι ⟨t, htK⟩ ∈ (T.subgroupOf K).map ι :=
        ⟨⟨t, htK⟩, Subgroup.mem_subgroupOf.2 htT, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hπ : π ⟨t, htK⟩ = 1 := by
      have h1 : eX (π ⟨t, htK⟩) = 1 := Subtype.ext hι
      exact eX.injective (h1.trans (map_one eX).symm)
    have hcen : (⟨t, htK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      have h : (⟨t, htK⟩ : ↥K) ∈ π.ker := hπ
      rwa [show π.ker = Subgroup.center ↥K from QuotientGroup.ker_mk' _] at h
    have hdisj := IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ hTK2 hZ3
    have h1 : (⟨t, htK⟩ : ↥K) = 1 :=
      Subgroup.mem_bot.1 (hdisj.le_bot (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 htT, hcen⟩))
    have ht : t = 1 := congrArg Subtype.val h1
    exact ht1 (Subtype.ext ht)
  have hconjT : ∀ b : ↥B, ∀ x ∈ (T.subgroupOf K).map ι, f b * x * (f b)⁻¹ ∈ (T.subgroupOf K).map ι := by
    intro b x hx
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨normalizerConjAutOfMem K B hBN b t, ?_, ?_⟩
    · have ht' : (t : Y) ∈ T := ht
      show ((normalizerConjAutOfMem K B hBN b t : ↥K) : Y) ∈ T
      have hco : ((normalizerConjAutOfMem K B hBN b t : ↥K) : Y) = (b : Y) * t * (b : Y)⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe (H := K) (Subgroup.inclusion hBN b) t
      rw [hco]
      exact (Subgroup.mem_normalizer_iff.1 (hBT b.2) (t : Y)).1 ht'
    · obtain ⟨γ, hγf, hγρ⟩ := hρf b
      show ((eX (π (normalizerConjAutOfMem K B hBN b t)) : ↥X') : Equiv.Perm (Fin 513)) =
        f b * ((eX (π t) : ↥X') : Equiv.Perm (Fin 513)) * (f b)⁻¹
      rw [show π (normalizerConjAutOfMem K B hBN b t) = ψ b (π t) from
        normalizerConjAutOfMem_comp_mk K B hBN b t, ← hγf]
      have h1 : eX (ψ b (π t)) = MulAut.congr eX (ψ b) (eX (π t)) := by simp [MulAut.congr_apply]
      rw [h1, ← hγρ, rhoU38_apply]
  have hAN : f.range ≤ Subgroup.normalizer (((T.subgroupOf K).map ι : Subgroup (Equiv.Perm (Fin 513))) :
      Set (Equiv.Perm (Fin 513))) := by
    intro a ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconjT b x, fun hx => ?_⟩
    have h := hconjT b⁻¹ _ hx
    have heq : f b⁻¹ * (f b * x * (f b)⁻¹) * (f b⁻¹)⁻¹ = x := by
      rw [map_inv]
      group
    rwa [heq] at h
  obtain ⟨h9, hconj⟩ := u38_elemAb_normalizing_two hT0X hT02 hT0ne hAG hA hAN
  have hCea : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set Y)) := isElemAbelian_mono hBea inf_le_left
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hCea
  obtain ⟨n, hn⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hA
  have hB81 : 81 ≤ Nat.card B := by
    have h := hK.card
    norm_num at h
    exact h
  have hm2 : m ≤ 2 := by
    by_contra h
    push Not at h
    have h27 : 3 ^ 3 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) h
    rw [← hm] at h27
    exact absurd hcB (not_lt.2 h27)
  have hn2 : n ≤ 2 := by
    by_contra h
    push Not at h
    have h27 : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h
    rw [← hn] at h27
    exact absurd (h27.trans h9) (by norm_num)
  have hcard : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 9 ∧ Nat.card f.range = 9 := by
    rw [hBC, hm, hn] at hB81
    rw [hm, hn]
    revert hB81
    interval_cases m <;> interval_cases n <;> norm_num
  obtain ⟨hC9, hA9⟩ := hcard
  obtain ⟨g, hg, hgA⟩ := hconj hA9
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hgA
  have hb1 : f b ≠ 1 := by
    rw [hb]
    intro h
    apply D0_ne_one
    calc D0 = g * (g⁻¹ * D0 * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hfb3 : orderOf (f b) = 3 := orderOf_eq_prime (by rw [← map_pow, hb3, map_one]) hb1
  let EB : Subgroup ↥B := (Subgroup.zpowers (f b)).comap f
  have hbE : (b : Y) ∈ EB.map B.subtype := ⟨b, Subgroup.mem_zpowers (f b), rfl⟩
  have hEcard : Nat.card (EB.map B.subtype) = 27 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    let fE : ↥EB →* Equiv.Perm (Fin 513) := f.comp EB.subtype
    have h1 := Subgroup.card_ker_mul_card_range fE
    have hrange : fE.range = Subgroup.zpowers (f b) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        refine ⟨⟨b ^ k, ?_⟩, ?_⟩
        · show f (b ^ k) ∈ Subgroup.zpowers (f b)
          rw [map_zpow]
          exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
        · show f (b ^ k) = f b ^ k
          rw [map_zpow]
    have hker : Nat.card fE.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
      have hmap : (fE.ker.map EB.subtype).map B.subtype = B ⊓ Subgroup.centralizer (K : Set Y) := by
        ext y
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact (hfC (x : ↥B)).1 (MonoidHom.mem_ker.1 hx)
        · intro hy
          have hyB : y ∈ B := (Subgroup.mem_inf.1 hy).1
          have hf1 : f ⟨y, hyB⟩ = 1 := (hfC ⟨y, hyB⟩).2 hy
          refine ⟨⟨y, hyB⟩, ⟨⟨⟨y, hyB⟩, ?_⟩, MonoidHom.mem_ker.2 hf1, rfl⟩, rfl⟩
          show f ⟨y, hyB⟩ ∈ Subgroup.zpowers (f b)
          rw [hf1]
          exact Subgroup.one_mem _
      rw [← hmap, Subgroup.card_map_of_injective B.subtype_injective,
        Subgroup.card_map_of_injective EB.subtype_injective]
    rw [← h1, hker, hrange, Nat.card_zpowers, hfb3, hC9]
  have hKE : K ⊓ Subgroup.centralizer ((EB.map B.subtype : Subgroup Y) : Set Y) =
      K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := by
    ext k
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hk, hkE⟩
      refine ⟨hk, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff.1 hh]
      exact Subgroup.mem_centralizer_iff.1 hkE _ hbE
    · rintro ⟨hk, hkb⟩
      refine ⟨hk, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
      obtain ⟨x, hx, rfl⟩ := he
      have hx' : f x ∈ Subgroup.zpowers (f b) := hx
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hx'
      have hc1 : f (x * (b ^ j)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hj, mul_inv_cancel]
      have hcK : ((x * (b ^ j)⁻¹ : ↥B) : Y) ∈ Subgroup.centralizer (K : Set Y) :=
        (Subgroup.mem_inf.1 ((hfC _).1 hc1)).2
      have hck : k * ((x * (b ^ j)⁻¹ : ↥B) : Y) = ((x * (b ^ j)⁻¹ : ↥B) : Y) * k :=
        Subgroup.mem_centralizer_iff.1 hcK k hk
      have hbk : Commute (b : Y) k := Subgroup.mem_centralizer_iff.1 hkb (b : Y) rfl
      have hxe : ((x : ↥B) : Y) = ((x * (b ^ j)⁻¹ : ↥B) : Y) * (b : Y) ^ j := by
        simp
      show ((x : ↥B) : Y) * k = k * ((x : ↥B) : Y)
      rw [hxe, mul_assoc, (Commute.zpow_left hbk j).eq, ← mul_assoc, ← hck, mul_assoc]
  obtain ⟨γ, hγf, hγρ⟩ := hρf b
  have hlay : GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y)) ≠ ⊥ := by
    intro hbot
    have h1 := (glaPLayer_inf_centralizer_eq_bot_iff Nat.prime_three hBN b).1 hbot
    have h2 := u38_glaPLayer_fix_conj_D0 hg γ (hγf.trans hb)
    rw [hγρ] at h2
    exact (glaPLayer_fixSubgroup_congr_ne_bot_iff Nat.prime_three eX (ψ b)).1 h2 h1
  refine ⟨EB.map B.subtype, Subgroup.map_subtype_le EB, isElemAbelian_mono hBea (Subgroup.map_subtype_le EB),
    hEcard.trans (by norm_num), ?_⟩
  rw [hKE]
  exact hlay

theorem kDescFam_u38_three : KDescFam 3 fU38 := by
  intro _ _ Y _ _ K B hK hc hcB
  exact Or.inl (kConcl_u38_three hK hc hcB)

end Certs

end CFSG.LocalAnalysis.GLTheoremA
