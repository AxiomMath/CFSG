module

public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8A
import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEC
import CFSG.ClassicalInvolution.Q3.Sec13End16M

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace AE8End

variable {Ω : Set (Subgroup G)} {u : G}

namespace SectData

private theorem e8h_hypGen {P Ω : Set (Subgroup G)} (H : End18.Hyp Ω)
    (hPΩ : P ⊆ Ω) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) :
    HypOmegaGen (restrictFamily P (pSpan P)) := by
  have h2P : ∀ L ∈ P,
      Subgroup.closure {x : G | x ∈ L ∧ IsPGroup 2 (Subgroup.zpowers x)} = L := by
    intro L hL
    apply le_antisymm
    · exact Subgroup.closure_le _ |>.mpr fun x hx => hx.1
    · intro x hx
      exact Subgroup.subset_closure
        ⟨hx, (H.endHyp.thmD.two L (hPΩ hL)).to_le (Subgroup.zpowers_le.mpr hx)⟩
  exact TL4.hypOmegaGen_restrict_of (pSpan P) (fun L hL => le_pSpan hL)
    (fun n hn L hL => hinv L hL n hn)
    (fun L hL => H.endHyp.thmD.hyp.omega1 L (hPΩ hL)) h2P
    (fun K hK J hJ => H.endHyp.thmD.hyp.omega3 K (hPΩ hK) J (hPΩ hJ))
    (fun K hK J hJ hne => H.endHyp.thmD.hyp.omega4 K (hPΩ hK) J (hPΩ hJ) hne)
    (fun K hK J hJ hne => H.endHyp.thmD.hyp.omega5 K (hPΩ hK) J (hPΩ hJ) hne)

private theorem e8h_conjSub_le {X W M : Subgroup G} {n : G}
    (hnorm : ∀ x ∈ X, ∀ q ∈ W, x * q * x⁻¹ ∈ W) (hn : n ∈ X) (hM : M ≤ W) :
    conjSub n M ≤ W := by
  intro y hy
  rw [mem_conjSub_iff] at hy
  have h1 := hnorm n hn _ (hM hy)
  simpa [mul_assoc] using h1

private theorem e8h_conj_cyc (M : Subgroup G) (n : G) (hc : IsCyclic ↥M) :
    IsCyclic ↥(conjSub n M) ∧ Nat.card ↥(conjSub n M) = Nat.card ↥M := by
  let e := Subgroup.equivMapOfInjective M (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
  exact ⟨(MulEquiv.isCyclic e).mp hc, (Nat.card_congr e.toEquiv).symm⟩

private theorem e8h_conjSub_eq_self {Q : Type*} [Group Q] {M : Subgroup Q} {q : Q}
    (hq : q⁻¹ = q) (hM : ∀ x ∈ M, q * x * q⁻¹ ∈ M) : conjSub q M = M := by
  have hqq : q * q = 1 := by
    have := mul_inv_cancel q
    rwa [hq] at this
  ext m
  rw [mem_conjSub_iff, hq]
  constructor
  · intro hm
    have h1 := hM _ hm
    rw [hq, show q * (q * m * q) * q = m by
      rw [show q * (q * m * q) * q = (q * q) * m * (q * q) by group, hqq, one_mul, mul_one]] at h1
    exact h1
  · intro hm
    have h1 := hM m hm
    rwa [hq] at h1

private theorem e8h_map_conjSub' {X Q : Type*} [Group X] [Group Q] (φ : X →* Q) (x : X)
    (M : Subgroup X) : (conjSub x M).map φ = conjSub (φ x) (M.map φ) := by
  ext q
  simp only [Subgroup.mem_map, mem_conjSub_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨x⁻¹ * y * x, hy, by simp only [map_mul, map_inv]⟩
  · rintro ⟨m, hm, hmq⟩
    refine ⟨x * m * x⁻¹, ?_, ?_⟩
    · rw [show x⁻¹ * (x * m * x⁻¹) * x = m by group]
      exact hm
    · rw [map_mul, map_mul, map_inv, hmq]
      group

private theorem e8h_map_conjSub {X : Subgroup G} {L : Subgroup G} {n : ℕ}
    (φ : ↥X →* AE.AEQ n) (x : ↥X) :
    ((conjSub (x : G) L).subgroupOf X).map φ = conjSub (φ x) ((L.subgroupOf X).map φ) := by
  rw [← conjSub_subgroupOf X x L]
  exact e8h_map_conjSub' φ x (L.subgroupOf X)

private theorem e8h_zBar_normalizes {n : ℕ} (hn : 5 ≤ n) {α β : Finset (Fin n)}
    (hα : α.card = 4) (hβ : β.card = 4) (hev : Even (α ∩ β).card) (b : Bool) :
    ∀ x ∈ AE.memBar α hα b, AE.zBar β hβ * x * (AE.zBar β hβ)⁻¹ ∈ AE.memBar α hα b := by
  rw [TC.Thin.zBar_eq_vbar_indv β hβ]
  refine (AE.vec_normalizes_memBar_iff hn α hα b (TC.Thin.indv β)).mpr ?_
  unfold TC.Thin.indv
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
  exact ZMod.natCast_eq_zero_iff_even.mpr hev

private theorem e8h_map_injective {Ω P : Set (Subgroup G)} (H : End18.Hyp Ω) (hP : P ⊆ Ω)
    {n : ℕ} (φ : ↥(pSpan P) →* AE.AEQ n)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan P)) {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    (he : (L.subgroupOf (pSpan P)).map φ = (L'.subgroupOf (pSpan P)).map φ) : L = L' := by
  by_contra hne
  have key : ∀ l' ∈ L', ∃ l ∈ L, ∃ c : G, (∀ y ∈ pSpan P, c * y = y * c) ∧ l' = l * c := by
    intro l' hl'
    have hx : φ ⟨l', le_pSpan hL' hl'⟩ ∈ (L.subgroupOf (pSpan P)).map φ := by
      rw [he]
      exact ⟨⟨l', le_pSpan hL' hl'⟩, Subgroup.mem_subgroupOf.mpr hl', rfl⟩
    obtain ⟨w, hw, hwe⟩ := hx
    have hk : w⁻¹ * ⟨l', le_pSpan hL' hl'⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwe, inv_mul_cancel]
    refine ⟨(w : G), Subgroup.mem_subgroupOf.mp hw, (w : G)⁻¹ * l',
      fun y hy => ?_, (mul_inv_cancel_left _ _).symm⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp (hker hk) ⟨y, hy⟩)).symm
  have hN : L' ≤ Subgroup.normalizer (L : Set G) := by
    intro l' hl'
    obtain ⟨l, hl, c, hc, rfl⟩ := key l' hl'
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer hl)
      (Subgroup.centralizer_le_normalizer _ ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hc x (le_pSpan hL hx)).symm
  have hL2 := H.endHyp.thmD.two L (hP hL)
  have hL'2 := H.endHyp.thmD.two L' (hP hL')
  obtain ⟨S, hS⟩ := (hL'2.to_sup_of_normal_right' hL2 hN).exists_le_sylow
  have hcomm : Commutes L L' := Q3CP.l67Gen G Ω H.endHyp.thmD.hyp S L
    (TC.mem_RSet_of_isPGroup (hP hL) hL2) L' (TC.mem_RSet_of_isPGroup (hP hL') hL'2)
    (le_sup_right.trans hS) (le_sup_left.trans hS) hne
  obtain ⟨v, hv, hvc⟩ := Sec6Gen.exists_noncentral H.endHyp.thmD.hyp (hP hL') le_rfl hL'2
    (by rw [H.endHyp.thmD.card L' (hP hL')]; norm_num)
  refine hvc fun w hw => ?_
  obtain ⟨l, hl, c, hc, rfl⟩ := key w hw
  calc v * (l * c) = v * l * c := (mul_assoc _ _ _).symm
    _ = l * v * c := by rw [hcomm l hl v hv]
    _ = l * (v * c) := mul_assoc _ _ _
    _ = l * (c * v) := by rw [hc v (le_pSpan hL' hv)]
    _ = l * c * v := (mul_assoc _ _ _).symm


private theorem e8h_cyc4 {P Ω : Set (Subgroup G)} (H : End18.Hyp Ω) (hPΩ : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    {W' : Subgroup ↥(pSpan P)} {η : Set (Subgroup ↥(pSpan P))} {S : Sylow 2 ↥(pSpan P)}
    (hη : η ∈ etaSet (restrictFamily P (pSpan P)) (S : Subgroup ↥(pSpan P)))
    (hinvη : ∀ s ∈ (S : Subgroup ↥(pSpan P)), ∀ U ∈ η, conjSub s U ∈ η)
    (hW' : W' = ⨆ V ∈ η, V)
    (hnorm : ∀ x ∈ pSpan P, ∀ q ∈ W'.map (pSpan P).subtype,
      x * q * x⁻¹ ∈ W'.map (pSpan P).subtype)
    {K : Subgroup G} (hK : K ∈ P) :
    ∃ A : Subgroup G, A ≤ K ∧ A ≤ W'.map (pSpan P).subtype ∧ IsCyclic ↥A ∧ Nat.card ↥A = 4 := by
  have hF2 := e8h_hypGen H hPΩ hinv
  have hηG : η ∈ etaG (restrictFamily P (pSpan P)) := ⟨S, hη, hinvη⟩
  have hηle : ∀ V ∈ η, V ≤ (S : Subgroup ↥(pSpan P)) := fun V hV => (hη.1 hV).2
  have hK2 : IsPGroup 2 (K.subgroupOf (pSpan P)) :=
    (H.endHyp.thmD.two K (hPΩ hK)).comap_subtype
  obtain ⟨S₀, hS₀⟩ := hK2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(pSpan P) S₀ S
  have hgS : conjSub g (K.subgroupOf (pSpan P)) ≤ (S : Subgroup ↥(pSpan P)) := by
    rw [← hg, Sec7.coe_smul_sylow]
    exact conjSub_mono hS₀
  rw [conjSub_subgroupOf] at hgS
  have hK₁P : conjSub (g : G) K ∈ P := hinv K hK g g.2
  have hK₁X : conjSub (g : G) K ≤ pSpan P := le_pSpan hK₁P
  have hK₁F : (conjSub (g : G) K).subgroupOf (pSpan P) ∈ restrictFamily P (pSpan P) :=
    ⟨conjSub (g : G) K, hK₁P, hK₁X, rfl⟩
  have hK₁card : Nat.card ↥((conjSub (g : G) K).subgroupOf (pSpan P)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₁X).toEquiv]
    exact H.endHyp.card_eq_eight (hPΩ hK₁P)
  have h611 := Sec6Gen.l6_11Gen ↥(pSpan P) (restrictFamily P (pSpan P)) hF2 S η hηG hηle
    ((conjSub (g : G) K).subgroupOf (pSpan P)) hK₁F
    (by rw [inf_eq_left.mpr hgS, hK₁card]; norm_num)
  have hA₁U : (conjSub (g : G) K).subgroupOf (pSpan P) ⊓ (⨆ V ∈ η, V) ∈
      USet (restrictFamily P (pSpan P)) := (hη.1 h611).1
  obtain ⟨R, -, J, hJ, hRJ, -, hcyc, hRcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hF2 hA₁U
  obtain ⟨L, hLP, hLX, rfl⟩ := hJ
  have hJ2 : IsPGroup 2 (L.subgroupOf (pSpan P)) :=
    (H.endHyp.thmD.two L (hPΩ hLP)).comap_subtype
  have hLcard : Nat.card ↥(L.subgroupOf (pSpan P)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv]
    exact H.endHyp.card_eq_eight (hPΩ hLP)
  have hRL : R = L.subgroupOf (pSpan P) := (IsSylow2In.eq_of_le hRJ hJ2 le_rfl hRJ.1).symm
  rw [hRL, hLcard] at hRcard
  set A₁ := (conjSub (g : G) K).subgroupOf (pSpan P) ⊓ (⨆ V ∈ η, V)
  have hA₁card : Nat.card ↥A₁ = 4 := by omega
  set A₁G := A₁.map (pSpan P).subtype
  have hA₁GK : A₁G ≤ conjSub (g : G) K := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp ha).1
  have hA₁GW : A₁G ≤ W'.map (pSpan P).subtype := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    rw [hW']
    exact (Subgroup.mem_inf.mp ha).2
  have hA₁Gc : IsCyclic ↥A₁G :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective A₁ (pSpan P).subtype
      (pSpan P).subtype_injective)).mp hcyc
  have hA₁Gn : Nat.card ↥A₁G = 4 := by
    rw [← hA₁card]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective A₁ (pSpan P).subtype
      (pSpan P).subtype_injective).toEquiv).symm
  have hK₁K : conjSub (g : G)⁻¹ (conjSub (g : G) K) = K := conjSub_inv_conjSub (g : G) K
  obtain ⟨hc, hn⟩ := e8h_conj_cyc A₁G (g : G)⁻¹ hA₁Gc
  refine ⟨conjSub (g : G)⁻¹ A₁G, ?_, ?_, hc, hn.trans hA₁Gn⟩
  · have := conjSub_mono (n := (g : G)⁻¹) hA₁GK
    rwa [hK₁K] at this
  · exact e8h_conjSub_le hnorm ((pSpan P).inv_mem g.2) hA₁GW

private theorem e8h_normalizes {P Ω : Set (Subgroup G)} (H : End18.Hyp Ω) (hPΩ : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    {WY : Subgroup G} (hWX : WY ≤ pSpan P) (hab : ∀ x ∈ WY, ∀ y ∈ WY, x * y = y * x)
    {K : Subgroup G} (hK : K ∈ P) {A : Subgroup G} (hAK : A ≤ K) (hAW : A ≤ WY)
    (hA4 : Nat.card ↥A = 4) {x : G} (hx : x ∈ WY) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  have hconj : conjSub x K ∈ P := hinv K hK x (hWX hx)
  rw [mem_normalizer_iff_conjSub_eq]
  by_contra hne
  have hA : A ≤ K ⊓ conjSub x K := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨hAK ha, ?_⟩
    rw [mem_conjSub_iff]
    have hcomm : x * a = a * x := hab x hx a (hAW ha)
    have h1 : x⁻¹ * a * x = a := by rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    rw [h1]
    exact hAK ha
  have hdvd : 4 ∣ Nat.card ↥(K ⊓ conjSub x K) := by
    rw [← hA4]
    exact Subgroup.card_dvd_of_le hA
  have hpos : Nat.card ↥(K ⊓ conjSub x K) ≠ 0 := Nat.card_pos.ne'
  have h22 : 2 ^ 2 ∣ Nat.card ↥(K ⊓ conjSub x K) := by
    norm_num
    exact hdvd
  have h2 : 2 ≤ padicValNat 2 (Nat.card ↥(K ⊓ conjSub x K)) :=
    (padicValNat_dvd_iff_le hpos).mp h22
  have h1 := (H.endHyp.thmD.hyp.omega4 K (hPΩ hK) (conjSub x K) (hPΩ hconj)
    (Ne.symm hne)).1
  omega

private theorem e8h_mem_omegaStar {P Ω : Set (Subgroup G)} (H : End18.Hyp Ω) (hPΩ : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    {WY : Subgroup G} (hWX : WY ≤ pSpan P) (hab : ∀ x ∈ WY, ∀ y ∈ WY, x * y = y * x)
    {J L : Subgroup G} (hJ : J ∈ P) (hL : L ∈ P) (hJL : J ≠ L)
    {A : Subgroup G} (hAJ : A ≤ J) (hAW : A ≤ WY) (hcyc : IsCyclic ↥A) (hA4 : Nat.card ↥A = 4)
    {AL : Subgroup G} (hALL : AL ≤ L) (hALW : AL ≤ WY) (hALn : Nat.card ↥AL = 4) :
    J ∈ omegaStarNbr Ω L := by
  have hJ2 : IsPGroup 2 J := H.endHyp.thmD.two J (hPΩ hJ)
  have hJcard : Nat.card ↥J = 8 := H.endHyp.card_eq_eight (hPΩ hJ)
  have hrel : A.relIndex J = 2 := by
    have h1 := Subgroup.relIndex_mul_card A J
    rw [inf_eq_left.mpr hAJ, hA4, hJcard] at h1
    omega
  have hAU : A ∈ USet Ω :=
    ⟨J, TC.mem_RSet_of_isPGroup (hPΩ hJ) hJ2, hAJ, hcyc, hrel⟩
  refine ⟨hPΩ hJ, hJL, A, hAU, hAJ, fun a ha => ?_⟩
  exact e8h_normalizes H hPΩ hinv hWX hab hL hALL hALW hALn (hAW ha)

private theorem e8h_sl3_moves (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    ∃ N : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Matrix.mulVec (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) v ≠ v := by
  have hdet : ∀ i j : Fin 3, i ≠ j → (1 + Matrix.single i j (1 : ZMod 2)).det = 1 := by
    decide
  have hmv : ∀ w : Fin 3 → ZMod 2, w ≠ 0 → ∃ j : Fin 3, w j ≠ 0 := by decide
  have hsucc : ∀ j : Fin 3, j + 1 ≠ j := by decide
  have hmove : ∀ w : Fin 3 → ZMod 2, ∀ j : Fin 3, w j ≠ 0 →
      Matrix.mulVec (1 + Matrix.single (j + 1) j (1 : ZMod 2)) w ≠ w := by
    decide
  obtain ⟨j, hj⟩ := hmv v hv
  exact ⟨⟨1 + Matrix.single (j + 1) j 1, hdet _ _ (hsucc j)⟩, hmove v j hj⟩

private theorem e8h_false_of_aeIdentOn (H : End18.Hyp Ω) (hu : SectData Ω u) {n : ℕ}
    (hn : 5 ≤ n) {𝒜 : Set (Finset (Fin n))} (hev : ∀ α ∈ 𝒜, ∀ β ∈ 𝒜, Even (α ∩ β).card)
    {Hs : Subgroup (AE.AEQ n)} (I : AEIdentOn (Generic.centMembers Ω u) n 𝒜 Hs) : False := by
  obtain ⟨L₀, hL₀, J₀, hJ₀, hbad1, hbad2⟩ := hu.bad
  have hPΩ : Generic.centMembers Ω u ⊆ Ω := fun L hL => hL.1
  obtain ⟨z, hz⟩ := (H.endHyp.thmD.hyp.omega1 J₀ (hPΩ hJ₀)).1
  obtain ⟨α, hα𝒜, hα, b, hLlab⟩ := I.label L₀ hL₀
  obtain ⟨β, hβ𝒜, hβ, _, hJlab⟩ := I.label J₀ hJ₀
  have hzY : z ∈ pSpan (Generic.centMembers Ω u) := le_pSpan hJ₀ hz.mem
  have hzc : Commute z u :=
    Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le (fun _ hM => hM.2) hzY)
  have hconjP : conjSub z L₀ ∈ Generic.centMembers Ω u := ae8a_conjSub_mem H hzc hL₀
  have hφz : I.φ ⟨z, hzY⟩ = AE.zBar β hβ :=
    TC.Thin.phi_map_eq_zBar I.φ hn hJ₀ (H.endHyp.card_eq_eight (hPΩ hJ₀)) hJlab hz
  have hzinv : (AE.zBar β hβ)⁻¹ = AE.zBar β hβ :=
    inv_eq_of_mul_eq_one_right (AE.zBar_mul_self β hβ)
  have hnorm : conjSub (I.φ ⟨z, hzY⟩)
      ((L₀.subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ) =
      (L₀.subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ := by
    rw [hφz, hLlab]
    exact e8h_conjSub_eq_self hzinv (e8h_zBar_normalizes hn hα hβ (hev α hα𝒜 β hβ𝒜) b)
  have himg : ((conjSub z L₀).subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ =
      (L₀.subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ := by
    have hm := e8h_map_conjSub (L := L₀) I.φ ⟨z, hzY⟩
    dsimp only at hm
    rw [hm, hnorm]
  have hJeq : conjSub z L₀ = L₀ :=
    e8h_map_injective H hPΩ I.φ I.ker_le hconjP hL₀ himg
  have hzN : z ∈ Subgroup.normalizer (L₀ : Set G) := mem_normalizer_iff_conjSub_eq.mpr hJeq
  rcases (H.normalizes_iff (hPΩ hL₀) (hPΩ hJ₀) hz).mp hzN with htw | hst
  · exact hbad1 (by rw [H.kPerp_eq_twinSet (hPΩ hL₀)]; exact htw)
  · exact hbad2 hst

theorem not_single (hu : SectData Ω u) :
    ¬ ∀ L ∈ Generic.centMembers Ω u, ∀ L' ∈ Generic.centMembers Ω u, L = L' := by
  intro h
  obtain ⟨R, hRP, T, hTP, hTn, -⟩ := hu.adj
  exact hTn.2.1 (h T hTP R hRP)

theorem not_wIn_singleton (H : End18.Hyp Ω) (hu : SectData Ω u) :
    ¬ ∃ W : Subgroup G, WIn (Generic.centMembers Ω u) (pSpan (Generic.centMembers Ω u)) = {W} := by
  rintro ⟨W, hW⟩
  have hPΩ : Generic.centMembers Ω u ⊆ Ω := fun L hL => hL.1
  have hinv : ∀ L ∈ Generic.centMembers Ω u, ∀ x ∈ pSpan (Generic.centMembers Ω u),
      conjSub x L ∈ Generic.centMembers Ω u := fun L hL x hx =>
    ae8a_conjSub_mem H (Subgroup.mem_centralizer_singleton_iff.mp
      (pSpan_le (fun _ hM => hM.2) hx)) hL
  have hF2 := e8h_hypGen H hPΩ hinv
  have hWmem : W ∈ WIn (Generic.centMembers Ω u) (pSpan (Generic.centMembers Ω u)) := by
    rw [hW]
    exact Set.mem_singleton W
  obtain ⟨W', hW'mem, hW'W⟩ := hWmem
  have hW'uniq : ∀ W'' ∈ WSet (restrictFamily (Generic.centMembers Ω u)
      (pSpan (Generic.centMembers Ω u))), W'' = W' := by
    intro W'' h
    have h1 : W''.map (pSpan (Generic.centMembers Ω u)).subtype ∈
        WIn (Generic.centMembers Ω u) (pSpan (Generic.centMembers Ω u)) := ⟨W'', h, rfl⟩
    rw [hW, Set.mem_singleton_iff] at h1
    exact Subgroup.map_injective (pSpan (Generic.centMembers Ω u)).subtype_injective
      (h1.trans hW'W.symm)
  have hnorm' : ∀ g : ↥(pSpan (Generic.centMembers Ω u)), conjSub g W' = W' := fun g =>
    hW'uniq _ (WSet.conj hF2.conjInvariant hW'mem g)
  subst hW'W
  have hnorm : ∀ x ∈ pSpan (Generic.centMembers Ω u),
      ∀ q ∈ W'.map (pSpan (Generic.centMembers Ω u)).subtype,
      x * q * x⁻¹ ∈ W'.map (pSpan (Generic.centMembers Ω u)).subtype := by
    rintro x hx _ ⟨q, hq, rfl⟩
    have h1 : (⟨x, hx⟩ : ↥(pSpan (Generic.centMembers Ω u))) * q *
        (⟨x, hx⟩ : ↥(pSpan (Generic.centMembers Ω u)))⁻¹ ∈
        conjSub (⟨x, hx⟩ : ↥(pSpan (Generic.centMembers Ω u))) W' :=
      conj_mem_conjSub hq
    rw [hnorm'] at h1
    exact ⟨_, h1, rfl⟩
  obtain ⟨η, ⟨S, hη, hinvη⟩, hW'eq⟩ := hW'mem
  have hab' : ∀ x ∈ W', ∀ y ∈ W', x * y = y * x := by
    have hetaeq : TC.etaSpan η = W' := hW'eq.symm
    intro x hx y hy
    rw [← hetaeq] at hx hy
    exact TC.etaSpan_comm hF2 ⟨S, hη, hinvη⟩ x hx y hy
  have hab : ∀ x ∈ W'.map (pSpan (Generic.centMembers Ω u)).subtype,
      ∀ y ∈ W'.map (pSpan (Generic.centMembers Ω u)).subtype, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hab' x hx y hy]
  have hWX : W'.map (pSpan (Generic.centMembers Ω u)).subtype ≤
      pSpan (Generic.centMembers Ω u) := Subgroup.map_subtype_le _
  have hcyc4 : ∀ K ∈ Generic.centMembers Ω u, ∃ A : Subgroup G, A ≤ K ∧
      A ≤ W'.map (pSpan (Generic.centMembers Ω u)).subtype ∧ IsCyclic ↥A ∧
        Nat.card ↥A = 4 :=
    fun K hK => e8h_cyc4 H hPΩ hinv hη hinvη hW'eq hnorm hK
  obtain ⟨L₀, hL₀, J₀, hJ₀, hbad1, hbad2⟩ := hu.bad
  have hne : J₀ ≠ L₀ := by
    intro h
    subst h
    exact hbad1 (Set.mem_insert _ _)
  obtain ⟨A, hAJ, hAW, hcyc, hA4⟩ := hcyc4 J₀ hJ₀
  obtain ⟨AL, hALL, hALW, -, hALn⟩ := hcyc4 L₀ hL₀
  exact hbad2 (e8h_mem_omegaStar H hPΩ hinv hWX hab hJ₀ hL₀ hne hAJ hAW hcyc hA4
    hALL hALW hALn)

theorem not_e8Struct (hu : SectData Ω u) :
    ¬ ∃ E : Subgroup G, E8Struct (pSpan (Generic.centMembers Ω u)) E := by
  rintro ⟨E, hE⟩
  have hYc : ∀ x ∈ pSpan (Generic.centMembers Ω u), Commute x u := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le (fun _ hM => hM.2) hx)
  have huE : u ∈ E := hE.cent u hu.mem_span fun e he => (hYc e (hE.le he)).eq.symm
  obtain ⟨e, he⟩ := TL4.exists_e8Basis hE.sq hE.card
  obtain ⟨v, hv⟩ := TL4.exists_e8Coord_eq he huE
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hu.ne_one (by rw [← hv, TL4.e8Coord_zero])
  have hfix : ∀ x : ↥(pSpan (Generic.centMembers Ω u)),
      Matrix.mulVec (TL4.e8Hom hE he x).1 v = v := by
    intro x
    apply TL4.e8Coord_injective he
    rw [← TL4.conj_e8Coord_e8Hom hE he x v, hv, (hYc (x : G) x.2).eq, mul_assoc,
      mul_inv_cancel, mul_one]
  have hall : ∀ N : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Matrix.mulVec (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) v = v := by
    intro N
    obtain ⟨x, hx⟩ := TL4.e8Hom_surjective hE he N
    have h1 := hfix x
    rwa [congrArg Subtype.val hx] at h1
  obtain ⟨N, hN⟩ := e8h_sl3_moves v hv0
  exact hN (hall N)

theorem isEmpty_aeIdentOn_e64 (H : End18.Hyp Ω) (hu : SectData Ω u) :
    IsEmpty (AEIdentOn (Generic.centMembers Ω u) 7 AE.e64Sets AE.e64Sub) := by
  have hev : ∀ α ∈ AE.e64Sets, ∀ β ∈ AE.e64Sets, Even (α ∩ β).card := by
    intro α hα β hβ
    by_cases h : α = β
    · subst h
      rw [Finset.inter_self, TL4.SecIdE2.card_of_mem_e64Sets hα]
      exact ⟨2, rfl⟩
    · rcases TL4.SecIdE2.adj4_of_mem_e64Sets hα hβ h with h2 | hd
      · rw [h2]
        exact ⟨1, rfl⟩
      · rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
        simp
  exact ⟨fun I => e8h_false_of_aeIdentOn H hu (by norm_num) hev I⟩

theorem isEmpty_aeIdentOn_e29 (H : End18.Hyp Ω) (hu : SectData Ω u) :
    IsEmpty (AEIdentOn (Generic.centMembers Ω u) 8 AE.e29Sets AE.e29Sub) := by
  have hev : ∀ α ∈ AE.e29Sets, ∀ β ∈ AE.e29Sets, Even (α ∩ β).card := by
    intro α hα β hβ
    by_cases h : α = β
    · subst h
      rw [Finset.inter_self, TL4.SecIdE2.card_of_mem_e29Sets hα]
      exact ⟨2, rfl⟩
    · rcases TL4.SecIdE2.adj4_of_mem_e29Sets hα hβ h with h2 | hd
      · rw [h2]
        exact ⟨1, rfl⟩
      · rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
        simp
  exact ⟨fun I => e8h_false_of_aeIdentOn H hu (by norm_num) hev I⟩

theorem exists_aeIdent (H : End18.Hyp Ω) (hu : SectData Ω u) :
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty (AEIdent (Generic.centMembers Ω u) m) := by
  rcases StarHyp.sectionConcl_centMembers H.endHyp.toStarHyp hu.ne_one with
    ⟨⟨L, hL, L', hL', hnc⟩, -⟩ | ⟨-, -, hout⟩
  · exact absurd (oneClass H hu L hL L' hL') hnc
  · unfold SectionOutcome at hout
    rcases hout with hs | hw | he | hI | hm | hI
    · exact (not_single hu hs).elim
    · exact (not_wIn_singleton H hu hw).elim
    · exact (not_e8Struct hu he).elim
    · obtain ⟨I⟩ := hI
      exact ((isEmpty_aeIdentOn_e64 H hu).false I).elim
    · exact hm
    · obtain ⟨I⟩ := hI
      exact ((isEmpty_aeIdentOn_e29 H hu).false I).elim

end SectData

end AE8End

end CFSG.ClassicalInvolution.Q3.Sec13
