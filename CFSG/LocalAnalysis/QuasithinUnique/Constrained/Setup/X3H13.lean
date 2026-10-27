module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3H13Orbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerInvariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {N : Type*} [Group N] (ρ : N →* (V ≃ₗ[k] V)) (L A : Subgroup N) [L.Normal]

structure OrbitSemisimpleSection (B Z : Submodule k V) : Prop where
  invariant_B : ∀ n, ∀ b ∈ B, ρ n b ∈ B
  invariant_Z : ∀ n, ∀ z ∈ Z, ρ n z ∈ Z
  Z_eq : Z = B ⊓ fixSub ρ L
  B_eq_comm : commSub ρ L B = B
  B_ne_bot : B ≠ ⊥
  M_ne_bot : ¬ B ≤ fixSub ρ L
  semisimple : ∃ s : Finset (Submodule k (V ⧸ fixSub ρ L)), s.SupIndep id ∧
    s.sup id = B.map (fixSub ρ L).mkQ ∧ ∀ U ∈ s, IsNontrivialLSimple (cvAct ρ L) L U
  family : ∃ 𝒰 : Finset (Submodule k (V ⧸ fixSub ρ L)),
    (∀ U ∈ 𝒰, IsNontrivialLSimple (cvAct ρ L) L U ∧ Offender.IsInvariant (cvAct ρ L) A U) ∧
    (∀ n, ∀ U ∈ 𝒰, U.map (cvAct ρ L n : (V ⧸ fixSub ρ L) →ₗ[k] (V ⧸ fixSub ρ L)) ∈ 𝒰) ∧
    𝒰.sup id = B.map (fixSub ρ L).mkQ
  ker_B : ∀ a ∈ A, (∀ b ∈ B, ρ a b = b) ↔ a ∈ Subgroup.centralizer (L : Set N)
  ker_M : ∀ a ∈ A, (∀ m ∈ B.map (fixSub ρ L).mkQ, cvAct ρ L a m = m) ↔
    a ∈ Subgroup.centralizer (L : Set N)
  not_central : ¬ A ≤ Subgroup.centralizer (L : Set N)
  offender_M : ∃ hM : Offender.IsInvariant (cvAct ρ L) A (B.map (fixSub ρ L).mkQ),
    Nat.card ↥(B.map (fixSub ρ L).mkQ) ≤
      weight (MonoidHom.id (↥(B.map (fixSub ρ L).mkQ) ≃ₗ[k] ↥(B.map (fixSub ρ L).mkQ)))
        (resSub (cvAct ρ L) A (B.map (fixSub ρ L).mkQ) hM).range
  detect : ∀ n, (∀ m ∈ B.map (fixSub ρ L).mkQ, cvAct ρ L n m = m) → ∀ b ∈ B, ρ n b = b
  twist : ∀ n l, ∀ m : V ⧸ fixSub ρ L,
    cvAct ρ L n (cvAct ρ L l m) = cvAct ρ L (n * l * n⁻¹) (cvAct ρ L n m)
  invariant_M : ∀ n, ∀ m ∈ B.map (fixSub ρ L).mkQ, cvAct ρ L n m ∈ B.map (fixSub ρ L).mkQ

variable [CharP k 2]

theorem add_self_eq_zero_of_charTwo' {V' : Type*} [AddCommGroup V'] [Module k V'] (x : V') :
    x + x = 0 := by
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  rw [← two_smul k x, h2, zero_smul]

omit [L.Normal] in
theorem fix_of_commute_involution {V' : Type*} [AddCommGroup V'] [Module k V']
    {σ : N →* (V' ≃ₗ[k] V')} {U : Submodule k V'} (hU : IsLSimple σ L U) {a : N}
    (ha2 : a * a = 1) (hcomm : a ∈ Subgroup.centralizer (L : Set N))
    (haU : ∀ u ∈ U, σ a u ∈ U) : ∀ u ∈ U, σ a u = u := by
  have haa : ∀ x, σ a (σ a x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, ← map_mul, ha2, map_one]; rfl
  let K : Submodule k V' := U ⊓ LinearMap.ker ((σ a : V' →ₗ[k] V') - LinearMap.id)
  have hK : Offender.IsInvariant σ L K := by
    intro l hl u hu
    have hu' : σ a u = u := by
      have h0 : (((σ a : V' →ₗ[k] V') - LinearMap.id : V' →ₗ[k] V') u) = 0 := LinearMap.mem_ker.1 hu.2
      rw [LinearMap.sub_apply] at h0
      exact sub_eq_zero.1 h0
    have hc : σ l (σ a u) = σ a (σ l u) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
      have := (Subgroup.mem_centralizer_iff.1 hcomm) l hl
      rw [this]
    refine ⟨hU.1 l hl u hu.1, LinearMap.mem_ker.2 ?_⟩
    rw [LinearMap.sub_apply]
    show σ a (σ l u) - σ l u = 0
    rw [← hc, hu', sub_self]
  rcases hU.2.2 K hK inf_le_left with hbot | hfull
  · intro u hu
    have hv : σ a u - u ∈ K := by
      refine ⟨U.sub_mem (haU u hu) hu, LinearMap.mem_ker.2 ?_⟩
      rw [LinearMap.sub_apply]
      show σ a (σ a u - u) - (σ a u - u) = 0
      rw [map_sub, haa]
      have := add_self_eq_zero_of_charTwo' (k := k) (u - σ a u)
      rw [← this]
      abel
    rw [hbot, Submodule.mem_bot] at hv
    exact sub_eq_zero.1 hv
  · intro u hu
    have : u ∈ K := by rw [hfull]; exact hu
    have h2 : (((σ a : V' →ₗ[k] V') - LinearMap.id : V' →ₗ[k] V') u) = 0 := LinearMap.mem_ker.1 this.2
    rw [LinearMap.sub_apply] at h2
    exact sub_eq_zero.1 h2

omit [CharP k 2] in
theorem mem_centralizer_of_fix {B : Submodule k V} (hL : CFSG.IsQuasisimple ↥L)
    (hBL : Offender.IsInvariant ρ L B) (hnt : ¬ B ≤ fixSub ρ L) {a : N}
    (hfix : ∀ b ∈ B, ρ a b = b) : a ∈ Subgroup.centralizer (L : Set N) := by
  have hfix' : ∀ b ∈ B, ρ a⁻¹ b = b := fun b hb => by
    have := congrArg (ρ a⁻¹) (hfix b hb)
    rw [ρ_inv_apply] at this
    exact this.symm
  let K : Subgroup ↥L := centSub (ρ.comp L.subtype) B
  have hKn : K.Normal := by
    refine ⟨fun x hx g b hb => ?_⟩
    have hgb : ρ (g : N)⁻¹ b ∈ B := hBL _ (L.inv_mem g.2) b hb
    show ρ ((g * x * g⁻¹ : ↥L) : N) b = b
    have h1 : ρ (x : N) (ρ (g : N)⁻¹ b) = ρ (g : N)⁻¹ b := hx _ hgb
    calc ρ ((g * x * g⁻¹ : ↥L) : N) b = ρ g (ρ x (ρ (g : N)⁻¹ b)) := by
          simp [map_mul, map_inv]
      _ = b := by rw [h1]; exact ρ_apply_inv ρ g b
  have hKc : K ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hKn with htop | hle
    · exfalso
      apply hnt
      intro b hb l hl
      have : (⟨l, hl⟩ : ↥L) ∈ K := by rw [htop]; trivial
      exact this b hb
    · exact hle
  have hna : a ∈ Subgroup.normalizer (L : Set N) := by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top a
  have : Group.IsPerfect ↥L := hL.1
  have hact : CFSG.QuasithinUnique.Setup.X5.normalizerAct L ⟨a, hna⟩ = 1 := by
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.one_apply, CFSG.QuasithinUnique.Setup.X5.normalizerAct_apply_mk, QuotientGroup.eq]
    have hmem : l⁻¹ * CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨a, hna⟩ l ∈ K := by
      intro b hb
      show ρ (((l⁻¹ * CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨a, hna⟩ l : ↥L)) : N) b = b
      have hlb : ρ (l : N) (ρ a⁻¹ b) ∈ B := by rw [hfix' b hb]; exact hBL _ l.2 b hb
      calc ρ (((l⁻¹ * CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨a, hna⟩ l : ↥L)) : N) b
          = ρ (l : N)⁻¹ (ρ a (ρ l (ρ a⁻¹ b))) := by
            simp [map_mul, map_inv, CFSG.QuasithinUnique.Setup.X5.coe_conjOn]
        _ = b := by rw [hfix _ hlb, hfix' b hb]; exact ρ_inv_apply ρ l b
    have := (Subgroup.center ↥L).inv_mem (hKc hmem)
    simpa using this
  exact CFSG.QuasithinUnique.Setup.X5.mem_centralizer_of_normalizerAct_eq_one L hact

variable [Finite V] [Finite N]

theorem orbitSemisimpleSection (hρ : Function.Injective ρ) (hL : CFSG.IsQuasisimple ↥L)
    (_hAne : A ≠ ⊥) (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hLA : ⁅L, A⁆ = L)
    (hoff : Nat.card V ≤ weight ρ A)
    (hstrict : ∀ D : Subgroup N, ⊥ < D → D < A → weight ρ D < weight ρ A) :
    ∃ B Z : Submodule k V, OrbitSemisimpleSection ρ L A B Z := by
  classical
  have : Fintype N := Fintype.ofFinite N
  have hperf : Group.IsPerfect ↥L := hL.1
  have hnt : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL
  have hLnt : ¬ (⊤ : Submodule k V) ≤ fixSub ρ L := by
    intro hle
    obtain ⟨⟨l, hl⟩, hne⟩ := exists_ne (1 : ↥L)
    apply hne
    apply Subtype.ext
    apply hρ
    refine LinearEquiv.ext fun v => ?_
    simpa using hle (Submodule.mem_top (x := v)) l hl
  obtain ⟨I, hI⟩ := exists_good_perfect ρ L hperf hLnt
  have hAn : A ≤ Subgroup.normalizer (L : Set N) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  obtain ⟨hno, hch⟩ := noPQuotient_centralPChief_of_quasisimple hL Nat.prime_two
  have hmax : ∀ D : Subgroup N, D ≤ A → weight ρ D ≤ weight ρ A := by
    intro D hD
    rcases hD.lt_or_eq with hlt | heq
    · by_cases hbot : D = ⊥
      · rw [hbot, weight_bot]; exact hoff
      · exact (hstrict D (bot_lt_iff_ne_bot.2 hbot) hlt).le
    · rw [heq]
  have hgood : ∀ n : N, IsGoodModule ρ L (I.map (ρ n : V →ₗ[k] V)) := fun n =>
    hI.map (Subgroup.normalizer_eq_top (H := L) ▸ Subgroup.mem_top n)
  have hAinv : ∀ n : N, Offender.IsInvariant ρ A (I.map (ρ n : V →ₗ[k] V)) := fun n =>
    bestOffender_invariance_strict ρ L A hAn hAel hLA hno hch hmax hstrict (hgood n).inv
      (hgood n).comm (hgood n).irr
  have hBinv : ∀ n, ∀ b ∈ orbitSum ρ I, ρ n b ∈ orbitSum ρ I := fun n b hb =>
    orbitSum_isInvariant ρ I n trivial b hb
  have hCinv : ∀ n, ∀ z ∈ fixSub ρ L, ρ n z ∈ fixSub ρ L := fixSub_invariant ρ L
  have hMinv : ∀ n, ∀ m ∈ (orbitSum ρ I).map (fixSub ρ L).mkQ,
      cvAct ρ L n m ∈ (orbitSum ρ I).map (fixSub ρ L).mkQ := by
    rintro n _ ⟨b, hb, rfl⟩
    exact ⟨ρ n b, hBinv n b hb, (cvAct_mkQ ρ L n b).symm⟩
  let 𝒰 : Finset (Submodule k (V ⧸ fixSub ρ L)) :=
    (Finset.univ : Finset N).image (fun n => (I.map (ρ n : V →ₗ[k] V)).map (fixSub ρ L).mkQ)
  have hsimple : ∀ U ∈ 𝒰, IsNontrivialLSimple (cvAct ρ L) L U := by
    intro U hU
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hU
    exact isNontrivialLSimple_image ρ L (hgood n)
  have hAinvU : ∀ U ∈ 𝒰, Offender.IsInvariant (cvAct ρ L) A U := by
    intro U hU
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hU
    rintro a ha _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨ρ a (ρ n i), ?_, ?_⟩
    · exact hAinv n a ha _ ⟨i, hi, rfl⟩
    · exact (cvAct_mkQ ρ L a _).symm
  have hsup : 𝒰.sup id = (orbitSum ρ I).map (fixSub ρ L).mkQ := by
    unfold orbitSum
    rw [Submodule.map_iSup]
    rw [Finset.sup_image, Finset.sup_univ_eq_iSup]
    rfl
  have hfam : ∀ n, ∀ U ∈ 𝒰,
      U.map (cvAct ρ L n : (V ⧸ fixSub ρ L) →ₗ[k] (V ⧸ fixSub ρ L)) ∈ 𝒰 := by
    intro m U hU
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hU
    refine Finset.mem_image.2 ⟨m * n, Finset.mem_univ _, ?_⟩
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨(fixSub ρ L).mkQ (ρ n i), ⟨ρ n i, ⟨i, hi, rfl⟩, rfl⟩, ?_⟩
      show cvAct ρ L m ((fixSub ρ L).mkQ (ρ n i)) = (fixSub ρ L).mkQ (ρ (m * n) i)
      rw [cvAct_mkQ, map_mul]; rfl
    · rintro ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, rfl⟩
      refine ⟨ρ (m * n) i, ⟨i, hi, rfl⟩, ?_⟩
      show (fixSub ρ L).mkQ (ρ (m * n) i) = cvAct ρ L m ((fixSub ρ L).mkQ (ρ n i))
      rw [cvAct_mkQ, map_mul]; rfl
  obtain ⟨s, hs𝒰, hsind, hssup⟩ := exists_supIndep_subset (σ := cvAct ρ L) (L := L) 𝒰
    (fun U hU => (hsimple U hU).1)
  have hBL : Offender.IsInvariant ρ L (orbitSum ρ I) := fun l _ => hBinv l
  have hdetect : ∀ n : N, (∀ m ∈ (orbitSum ρ I).map (fixSub ρ L).mkQ, cvAct ρ L n m = m) →
      ∀ b ∈ orbitSum ρ I, ρ n b = b := by
    intro n hn b hb
    have := detect_of_trivial_mod ρ L ⊤ (Subgroup.normalizer_eq_top (H := L)).symm.le hno hch
      (orbitSum ρ I) hBL (fun a _ => hBinv a) (commSub_orbitSum ρ L hI) (b := n)
      (Subgroup.mem_top n) (by
        intro w hw
        have h1 := hn _ ⟨w, hw, rfl⟩
        rw [cvAct_mkQ] at h1
        have h2 : (fixSub ρ L).mkQ (ρ n w - w) = 0 := by rw [map_sub, h1, sub_self]
        exact (Submodule.Quotient.mk_eq_zero _).1 h2)
    exact this b hb
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    simpa [pow_two] using this
  have hfixM : ∀ a ∈ A, a ∈ Subgroup.centralizer (L : Set N) →
      ∀ m ∈ (orbitSum ρ I).map (fixSub ρ L).mkQ, cvAct ρ L a m = m := by
    intro a ha hc m hm
    rw [← hsup] at hm
    have hle : 𝒰.sup id ≤ LinearMap.ker
        ((cvAct ρ L a : (V ⧸ fixSub ρ L) →ₗ[k] (V ⧸ fixSub ρ L)) - LinearMap.id) := by
      refine Finset.sup_le fun U hU u hu => ?_
      have := fix_of_commute_involution L (hsimple U hU).1 (hA2 a ha) hc
        (fun u hu => hAinvU U hU a ha u hu) u hu
      refine LinearMap.mem_ker.2 ?_
      rw [LinearMap.sub_apply]
      show cvAct ρ L a u - u = 0
      rw [this, sub_self]
    have h0 := LinearMap.mem_ker.1 (hle hm)
    rw [LinearMap.sub_apply] at h0
    exact sub_eq_zero.1 h0
  have hkerB : ∀ a ∈ A, (∀ b ∈ orbitSum ρ I, ρ a b = b) ↔
      a ∈ Subgroup.centralizer (L : Set N) := by
    intro a ha
    constructor
    · intro hfix
      exact mem_centralizer_of_fix ρ L hL hBL (orbitSum_not_le_fix ρ L hI) hfix
    · intro hc
      exact hdetect a (hfixM a ha hc)
  have hkerM : ∀ a ∈ A, (∀ m ∈ (orbitSum ρ I).map (fixSub ρ L).mkQ, cvAct ρ L a m = m) ↔
      a ∈ Subgroup.centralizer (L : Set N) := by
    intro a ha
    constructor
    · intro hfix
      exact (hkerB a ha).1 (hdetect a hfix)
    · intro hc
      exact hfixM a ha hc
  have hMA : Offender.IsInvariant (cvAct ρ L) A ((orbitSum ρ I).map (fixSub ρ L).mkQ) :=
    fun a _ m hm => hMinv a m hm
  refine ⟨orbitSum ρ I, orbitSum ρ I ⊓ fixSub ρ L, ?_⟩
  refine ⟨hBinv, ?_, rfl, commSub_orbitSum ρ L hI, ?_, orbitSum_not_le_fix ρ L hI, ?_, ?_,
    hkerB, hkerM, ?_, ⟨hMA, ?_⟩, hdetect, ?_, hMinv⟩
  · intro n z hz
    exact ⟨hBinv n z hz.1, hCinv n z hz.2⟩
  · intro h
    apply hI.irr.1
    have h1 : I ≤ ⊥ := h ▸ le_orbitSum ρ I
    rw [le_bot_iff.1 h1]
    exact bot_le
  · exact ⟨s, hsind, hssup.trans hsup, fun U hU => hsimple U (hs𝒰 hU)⟩
  · exact ⟨𝒰, fun U hU => ⟨hsimple U hU, hAinvU U hU⟩, hfam, hsup⟩
  · intro h
    have h1 : ⁅A, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 h
    rw [Subgroup.commutator_comm, hLA] at h1
    obtain ⟨⟨l, hl⟩, hne⟩ := exists_ne (1 : ↥L)
    apply hne
    apply Subtype.ext
    rw [h1] at hl
    exact Subgroup.mem_bot.1 hl
  · set B := orbitSum ρ I with hBdef
    set C := fixSub ρ L with hCdef
    set M := B.map C.mkQ with hMdef
    let ρA : ↥A →* (V ≃ₗ[k] V) := ρ.comp A.subtype
    let πA : ↥A →* ((V ⧸ C) ≃ₗ[k] (V ⧸ C)) := (cvAct ρ L).comp A.subtype
    have hBA' : ∀ a : ↥A, ∀ w ∈ B, ρA a w ∈ B := fun a w hw => hBinv a w hw
    have hMA' : ∀ a : ↥A, ∀ w ∈ M, πA a w ∈ M := fun a w hw => hMinv a w hw
    have hmaxA : ∀ D : Subgroup ↥A, weight ρA D ≤ weight ρA ⊤ := by
      intro D
      show weight (ρ.comp A.subtype) D ≤ weight (ρ.comp A.subtype) ⊤
      rw [weight_comp_subtype, weight_comp_subtype, map_subtype_top]
      exact hmax _ (Subgroup.map_subtype_le D)
    obtain ⟨h1, -⟩ := fixedWeight_restrict ρA B hBA' hmaxA
    have h1' := h1 ⊥ bot_le
    rw [weight_bot, weightId_range] at h1'
    have hcs : centSub ρA B = centSub πA M := by
      ext a
      rw [mem_centSub, mem_centSub]
      constructor
      · rintro h _ ⟨b, hb, rfl⟩
        show cvAct ρ L a.1 (C.mkQ b) = C.mkQ b
        rw [cvAct_mkQ, show ρ a.1 b = b from h b hb]
      · intro h b hb
        exact hdetect a.1 (fun m hm => h m hm) b hb
    show Nat.card ↥M ≤ weight (MonoidHom.id (↥M ≃ₗ[k] ↥M)) (resHom πA M hMA').range
    rw [weightId_range, ← hcs]
    have hcard1 := natCard_map_mkQ_mul_natCard_inf C B
    set F := B ⊓ fixSub ρA ⊤ with hFdef
    have hcard2 := natCard_map_mkQ_mul_natCard_inf C F
    have hFM : F.map C.mkQ ≤ M ⊓ fixSub πA ⊤ := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx.1, rfl⟩, fun a _ => ?_⟩
      show cvAct ρ L a.1 (C.mkQ x) = C.mkQ x
      rw [cvAct_mkQ, show ρ a.1 x = x from hx.2 a (Subgroup.mem_top a)]
    have hle1 : Nat.card ↥(F.map C.mkQ) ≤ Nat.card ↥(M ⊓ fixSub πA ⊤) :=
      Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le hFM)
    have hle2 : Nat.card ↥(F ⊓ C) ≤ Nat.card ↥(B ⊓ C) :=
      Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le (inf_le_inf_right C inf_le_left))
    have hF : Nat.card ↥F ≤ Nat.card ↥(M ⊓ fixSub πA ⊤) * Nat.card ↥(B ⊓ C) := by
      rw [← hcard2]; exact Nat.mul_le_mul hle1 hle2
    have hpos : 0 < Nat.card ↥(B ⊓ C) := Nat.card_pos
    have hmain : Nat.card ↥M * Nat.card ↥(B ⊓ C) ≤
        ((centSub ρA B).index * Nat.card ↥(M ⊓ fixSub πA ⊤)) * Nat.card ↥(B ⊓ C) := by
      calc Nat.card ↥M * Nat.card ↥(B ⊓ C) = Nat.card ↥B := hcard1
        _ ≤ (centSub ρA B).index * Nat.card ↥F := h1'
        _ ≤ (centSub ρA B).index * (Nat.card ↥(M ⊓ fixSub πA ⊤) * Nat.card ↥(B ⊓ C)) :=
            Nat.mul_le_mul_left _ hF
        _ = ((centSub ρA B).index * Nat.card ↥(M ⊓ fixSub πA ⊤)) * Nat.card ↥(B ⊓ C) := by ring
    exact Nat.le_of_mul_le_mul_right hmain hpos
  · intro n l m
    show (cvAct ρ L n * cvAct ρ L l) m = (cvAct ρ L (n * l * n⁻¹) * cvAct ρ L n) m
    rw [← map_mul, ← map_mul]
    congr 2
    group

end CFSG.QuasithinUnique.Setup.X3
