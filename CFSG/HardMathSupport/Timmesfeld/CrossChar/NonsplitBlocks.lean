module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix Polynomial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Noncentral

theorem exists_pow_eq_one_notMem_center {E : Type*} [Field E] {m p : ℕ} (hm : 2 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2) {ω : E} (hω : IsPrimitiveRoot ω p) :
    ∃ s : SpecialLinearGroup (Fin m) E, s ^ p = 1 ∧
      s ∉ Subgroup.center (SpecialLinearGroup (Fin m) E) := by
  classical
  have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp
  have hω0 : ω ≠ 0 := hω.ne_zero hp.ne_zero
  let v : Fin m → E := fun i => if i = ⟨0, by omega⟩ then ω else
    if i = ⟨1, by omega⟩ then ω⁻¹ else 1
  have hdet : (Matrix.diagonal v).det = 1 := by
    rw [Matrix.det_diagonal]
    rw [Finset.prod_eq_mul (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ hne]
    · simp [v, hω0]
    · intro c _ hc
      simp [v, hc.1, hc.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  let s : SpecialLinearGroup (Fin m) E := ⟨Matrix.diagonal v, hdet⟩
  have hsp : s ^ p = 1 := by
    apply Subtype.ext
    change (Matrix.diagonal v) ^ p = 1
    rw [Matrix.diagonal_pow]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.one_apply_eq]
      by_cases h0 : i = ⟨0, by omega⟩
      · simp [v, h0, hω.pow_eq_one]
      · by_cases h1 : i = ⟨1, by omega⟩
        · simp [v, h1, hne.symm, inv_pow, hω.pow_eq_one]
        · simp [v, h0, h1]
    · simp [hij]
  refine ⟨s, hsp, fun hs => ?_⟩
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hs
  have e0 := congrFun (congrFun hr ⟨0, by omega⟩) ⟨0, by omega⟩
  have e1 := congrFun (congrFun hr ⟨1, by omega⟩) ⟨1, by omega⟩
  simp only [s, v, scalar_apply, Matrix.diagonal_apply_eq, ite_true, hne.symm, ite_false] at e0 e1
  have hωω : ω = ω⁻¹ := e0.symm.trans e1
  have h2 : ω ^ 2 = 1 := by
    rw [sq]
    calc ω * ω = ω * ω⁻¹ := congrArg (ω * ·) hωω
      _ = 1 := mul_inv_cancel₀ hω0
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hω.dvd_of_pow_eq_one 2 h2))

end Noncentral

section Blocks

variable {n : ℕ} {F : Type} [Field F] {x : Module.End F (Fin n → F)}
  {hsq : Squarefree (minpoly F x)} {h : primaryFactors x}

local notation "PSLn" => projectiveSL n F

@[expose] noncomputable def blockProj (hsq : Squarefree (minpoly F x)) (h : primaryFactors x) :
    Subgroup (projectiveSL n F) :=
  ((blockImage hsq h).comap SpecialLinearGroup.toGL).map (proj n F)

theorem commute_of_mem_blockImage_of_toLin' {M : GL (Fin n) F}
    (hM : Matrix.toLin' (M : Matrix (Fin n) (Fin n) F) = x) {g : GL (Fin n) F}
    (hg : g ∈ blockImage hsq h) : g * M = M * g := by
  have h1 := blockImage_le_range hsq h hg
  rwa [range_commutantUnitsToGL_eq_centralizer M hM, Subgroup.mem_centralizer_singleton_iff]
    at h1

theorem blockProj_conj_le {M : GL (Fin n) F}
    (hM : Matrix.toLin' (M : Matrix (Fin n) (Fin n) F) = x)
    {H : Subgroup (MulAut PSLn)} (hH : innerAut PSLn ≤ H) :
    (blockProj hsq h).map (MulAut.conj : PSLn →* MulAut PSLn) ≤
      H ⊓ Subgroup.centralizer ({conjAut n F M} : Set (MulAut PSLn)) := by
  rintro _ ⟨t, ⟨s, hs, rfl⟩, rfl⟩
  refine Subgroup.mem_inf.2 ⟨hH ⟨proj n F s, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← conjAut_toGL, ← map_mul, ← map_mul,
    commute_of_mem_blockImage_of_toLin' hM hs]

theorem blockComap_isQuasisimple (hgood : GoodBlock h) :
    CFSG.IsQuasisimple ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) := by
  have hrange := blockImage_le_range_toGL_of_good hsq h hgood
  let e0 : ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) ≃*
        blockImage hsq h :=
    (Subgroup.equivMapOfInjective _ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →*
      GL (Fin n) F) SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hrange))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e0.symm
    (isQuasisimple_blockImage_of_good hsq h hgood)

@[expose] noncomputable def blockToProj (hsq : Squarefree (minpoly F x)) (h : primaryFactors x) :
    ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) →*
        blockProj hsq h :=
  ((proj n F).comp ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)).subtype).codRestrict
    (blockProj hsq h) (fun y => ⟨y, y.2, rfl⟩)

theorem blockToProj_surjective : Function.Surjective (blockToProj hsq h) := by
  rintro ⟨_, s, hs, rfl⟩
  exact ⟨⟨s, hs⟩, rfl⟩

theorem ker_blockToProj_le_center :
    (blockToProj hsq h).ker ≤ Subgroup.center ((blockImage hsq h).comap
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F)) := by
  intro y hy
  have h1 : proj n F (y : SpecialLinearGroup (Fin n) F) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
  have h2 := scalars_le_center n F (proj_eq_one_iff.1 h1)
  rw [Subgroup.mem_center_iff]
  intro z
  exact Subtype.ext ((Subgroup.mem_center_iff.1 h2 (z : SpecialLinearGroup (Fin n) F)))

theorem blockProj_isQuasisimple (hgood : GoodBlock h) : CFSG.IsQuasisimple (blockProj hsq h) :=
  CFSG.LocalCores.isQuasisimple_of_surjective (blockComap_isQuasisimple hgood) _
    blockToProj_surjective ker_blockToProj_le_center

theorem blockProj_isComponent [Finite F] (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : PSLn →* MulAut PSLn)) {M : GL (Fin n) F}
    (hM : Matrix.toLin' (M : Matrix (Fin n) (Fin n) F) = x)
    {H : Subgroup (MulAut PSLn)} (hH : innerAut PSLn ≤ H) (hgood : GoodBlock h) :
    CFSG.IsComponent (((blockProj hsq h).map (MulAut.conj : PSLn →* MulAut PSLn)).subgroupOf
      (H ⊓ Subgroup.centralizer ({conjAut n F M} : Set (MulAut PSLn)))) := by
  have hTcC := blockProj_conj_le (hsq := hsq) (h := h) hM hH
  refine ⟨?_, ?_⟩
  · have e1 := (blockProj hsq h).equivMapOfInjective (MulAut.conj : PSLn →* MulAut PSLn) hinj
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (e1.trans (Subgroup.subgroupOfEquivOfLe hTcC).symm) (blockProj_isQuasisimple hgood)
  · set e : MulAut PSLn := conjAut n F M with he
    set C0 : Subgroup (SpecialLinearGroup (Fin n) F) :=
      (Subgroup.centralizer ({M} : Set (GL (Fin n) F))).comap SpecialLinearGroup.toGL with hC0
    refine isSubnormal_subgroupOf_of_chain
      (B := (C0.map (proj n F)).map (MulAut.conj : PSLn →* MulAut PSLn))
      (D := innerAut PSLn ⊓ Subgroup.centralizer ({e} : Set (MulAut PSLn))) ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨t, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨_, ⟨s, Subgroup.mem_centralizer_singleton_iff.2
        (commute_of_mem_blockImage_of_toLin' hM hs), rfl⟩, rfl⟩
    · rintro _ ⟨t, ⟨c, hc, rfl⟩, rfl⟩
      refine Subgroup.mem_inf.2 ⟨⟨proj n F c, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, he, ← conjAut_toGL, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.1 hc]
    · intro y hy
      exact Subgroup.mem_inf.2 ⟨hH (Subgroup.mem_inf.1 hy).1, (Subgroup.mem_inf.1 hy).2⟩
    · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩ _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨proj n F (c * s * c⁻¹), ⟨c * s * c⁻¹, ?_, rfl⟩, ?_⟩
      · change SpecialLinearGroup.toGL (c * s * c⁻¹) ∈ blockImage hsq h
        rw [map_mul, map_mul, map_inv]
        refine conj_mem_blockImage hsq h ?_ hs
        rw [range_commutantUnitsToGL_eq_centralizer M hM]
        exact hc
      · simp [map_mul, map_inv]
    · rintro y ⟨⟨k, rfl⟩, hy⟩ _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      obtain ⟨u, rfl⟩ := proj_surjective n F k
      set U : GL (Fin n) F := SpecialLinearGroup.toGL u with hU
      have hyM : conjAut n F U * conjAut n F M = conjAut n F M * conjAut n F U := by
        rw [hU, conjAut_toGL]
        exact Subgroup.mem_centralizer_singleton_iff.1 hy
      have h1 : conjAut n F (U * M * U⁻¹ * M⁻¹) * fieldAut n F 1 = 1 := by
        rw [map_one, mul_one, map_mul, map_mul, map_mul, map_inv, map_inv, hyM]
        group
      obtain ⟨z, hz⟩ := (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 h1).2
      have hzc : GeneralLinearGroup.scalar (Fin n) z ∈ Subgroup.center (GL (Fin n) F) :=
        Subgroup.mem_center_iff.2 fun g => (GeneralLinearGroup.scalar_commute z g).symm
      have hua : U * M * U⁻¹ = GeneralLinearGroup.scalar (Fin n) z * M := by
        rw [hz]
        group
      have hc' := conj_mem_centralizer_of_central hzc hua
        (Subgroup.mem_centralizer_singleton_iff.1 hc)
      refine ⟨proj n F (u * c * u⁻¹), ⟨u * c * u⁻¹, ?_, rfl⟩, ?_⟩
      · change SpecialLinearGroup.toGL (u * c * u⁻¹) ∈ Subgroup.centralizer ({M} : Set _)
        rw [map_mul, map_mul, map_inv, Subgroup.mem_centralizer_singleton_iff]
        exact hc'
      · simp [map_mul, map_inv]
    · intro y hy z hz
      obtain ⟨⟨k, rfl⟩, hze⟩ := Subgroup.mem_inf.1 hz
      have hye := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2
      have hze' := Subgroup.mem_centralizer_singleton_iff.1 hze
      refine Subgroup.mem_inf.2 ⟨⟨(y : MulAut PSLn) k, ?_⟩, ?_⟩
      · rw [← mul_conj_mul_inv]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (((Commute.mul_left (show Commute y e from hye) (show Commute _ e from hze')).mul_left
          (show Commute y⁻¹ e from (show Commute y e from hye).inv_left)).eq)

theorem dvd_card_blockProj {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hgood : GoodBlock h) {ω : F}
    (hω : IsPrimitiveRoot ω p) : p ∣ Nat.card (blockProj hsq h) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hm : 2 ≤ mult x h := by rcases hgood with h' | ⟨h', _⟩ <;> omega
  have hω' : IsPrimitiveRoot (algebraMap F (Efac x h) ω) p :=
    hω.map_of_injective (algebraMap F (Efac x h)).injective
  obtain ⟨s, hsp, hsZ⟩ := exists_pow_eq_one_notMem_center hm hp hp2 hω'
  have hrange := blockImage_le_range_toGL_of_good hsq h hgood
  have hg : blockTheta hsq (blockEmbed (Efac x) (mult x) h s) ∈ blockImage hsq h :=
    mem_blockImage.2 ⟨s, rfl⟩
  obtain ⟨b, hb⟩ := hrange hg
  have hbmem : proj n F b ∈ blockProj hsq h :=
    ⟨b, show SpecialLinearGroup.toGL b ∈ blockImage hsq h by rw [hb]; exact hg, rfl⟩
  have hbp : proj n F b ^ p = 1 := by
    have : b ^ p = 1 := SpecialLinearGroup.toGL_injective (by
      rw [map_pow, hb, map_one, ← map_pow, ← map_pow, hsp, map_one, map_one])
    rw [← map_pow, this, map_one]
  have hb1 : proj n F b ≠ 1 := by
    intro h1
    have hbZ := scalars_le_center n F (proj_eq_one_iff.1 h1)
    apply hsZ
    rw [Subgroup.mem_center_iff]
    intro s'
    have hg' : blockTheta hsq (blockEmbed (Efac x) (mult x) h s') ∈ blockImage hsq h :=
      mem_blockImage.2 ⟨s', rfl⟩
    obtain ⟨b', hb'⟩ := hrange hg'
    have h2 : b' * b = b * b' := Subgroup.mem_center_iff.1 hbZ b'
    have h3 : blockTheta hsq (blockEmbed (Efac x) (mult x) h (s' * s)) =
        blockTheta hsq (blockEmbed (Efac x) (mult x) h (s * s')) := by
      rw [map_mul, map_mul, map_mul, map_mul, ← hb', ← hb, ← map_mul, ← map_mul, h2]
    exact blockEmbed_injective h (blockTheta_injective hsq h3)
  rw [← orderOf_eq_prime hbp hb1]
  exact Subgroup.orderOf_dvd_natCard _ hbmem

theorem blockProj_le_fixSub [Finite F] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M : GL (Fin n) F} (hM : Matrix.toLin' (M : Matrix (Fin n) (Fin n) F) = x)
    {H E : Subgroup (MulAut PSLn)} (hH : innerAut PSLn ≤ H) {g : MulAut PSLn}
    (hg : g ∈ localDeltaIn p H E) (hME : conjAut n F M ∈ E) (hM1 : conjAut n F M ≠ 1)
    (hgood : GoodBlock h) {ω : F} (hω : IsPrimitiveRoot ω p) :
    blockProj hsq h ≤ fixSub g := by
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F) hn
  exact le_fixSub_of_component hp hinj hg hME hM1 (blockProj_conj_le hM hH)
    (blockProj_isComponent hn hinj hM hH hgood)
    (fun hcop => (Nat.Prime.coprime_iff_not_dvd hp).1 hcop (dvd_card_blockProj hp hp2 hgood hω))

theorem blockImage_le_map_fixSub [Finite F] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M : GL (Fin n) F} (hM : Matrix.toLin' (M : Matrix (Fin n) (Fin n) F) = x)
    {H E : Subgroup (MulAut PSLn)} (hH : innerAut PSLn ≤ H) {g : MulAut PSLn}
    (hg : g ∈ localDeltaIn p H E) (hME : conjAut n F M ∈ E) (hM1 : conjAut n F M ≠ 1)
    (hgood : GoodBlock h) {ω : F} (hω : IsPrimitiveRoot ω p) :
    blockImage hsq h ≤ ((fixSub g).comap (proj n F)).map SpecialLinearGroup.toGL := by
  intro b hb
  obtain ⟨s, hs⟩ := blockImage_le_range_toGL_of_good hsq h hgood hb
  refine ⟨s, ?_, hs⟩
  exact blockProj_le_fixSub hn hp hp2 hM hH hg hME hM1 hgood hω
    ⟨s, show SpecialLinearGroup.toGL s ∈ blockImage hsq h by rw [hs]; exact hb, rfl⟩

theorem eq_one_of_comap_fixSub_eq_top {g : MulAut PSLn} (h : (fixSub g).comap (proj n F) = ⊤) :
    g = 1 := by
  rw [← fixSub_eq_top_iff]
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨s, rfl⟩ := proj_surjective n F y
  exact (h ▸ Subgroup.mem_top s : s ∈ (fixSub g).comap (proj n F))

end Blocks

end CFSG.HardMathSupport.Timmesfeld.CrossChar
