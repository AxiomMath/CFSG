module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GVac
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264sU38Three
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264sU38

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.LocalAnalysis.GLTheoremA.U38ThreeModel

section Certs


theorem t263_u38_concl {Y : Type} [Group Y] [Finite Y] {K B : Subgroup Y} (hK : T263VHyp 3 K B)
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

theorem t263Desc_u38 : T263Desc t263GU38 := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T' hT'ne hT'2 hT'S
    hBT' hker x hxB₀ hxC hxcomm
  have hvh := t263VHyp_of_data hSn hSq hSp hB hp h4 hT
  have hcat : catalogIs (↥S ⧸ Subgroup.center ↥S) fU38 := S10.catalogIs_imp (fun _ h => h) hQ
  by_cases hp3 : p = 3
  · subst hp3
    exact Or.inl (Or.inl (t263_u38_concl hvh hcat hC))
  · exfalso
    have hdvd := card_mulAut_dvd_u38 (S := ↥S ⧸ Subgroup.center ↥S) hcat
    exact t263_false_of_not_sq_dvd hp hvh hC (MulEquiv.refl _) fun hsq => not_sq_dvd_u38 hp hp2 hp3 (hsq.trans hdvd)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263

end
