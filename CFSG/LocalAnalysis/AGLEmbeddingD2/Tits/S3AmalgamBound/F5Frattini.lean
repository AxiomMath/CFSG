module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowFrattiniSup
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFFusion
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFPreimage
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

theorem frattini_amb {Ω : Type*} [Group Ω] [Finite Ω] {A Y P : Subgroup Ω} (hYA : Y ≤ A)
    (hYn : A ≤ Subgroup.normalizer (Y : Set Ω)) (hP : IsSylowTwoOf P Y) :
    ∀ a ∈ A, ∃ y ∈ Y, ∃ n ∈ A ⊓ Subgroup.normalizer (P : Set Ω), a = y * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPY, hP2, hPidx⟩ := hP
  set N : Subgroup ↥A := Y.subgroupOf A with hN
  have : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYA).2 hYn
  set P₁ : Subgroup ↥N := (P.subgroupOf A).subgroupOf N with hP₁
  have hP₁2 : IsPGroup 2 P₁ := by
    intro x
    have hxP : (((x : ↥N) : ↥A) : Ω) ∈ P :=
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 x.2)
    obtain ⟨k, hk⟩ := hP2 ⟨((x : ↥N) : ↥A).1, hxP⟩
    refine ⟨k, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
    simpa using congrArg Subtype.val hk
  have hP₁idx : ¬ 2 ∣ P₁.index := by
    have h := Subgroup.relIndex_subgroupOf (H := P) (K := Y) (L := A) hYA
    have h' : P₁.index = P.relIndex Y := h
    rw [h']; exact hPidx
  let S : Sylow 2 ↥N := hP₁2.toSylow hP₁idx
  have hF := Sylow.normalizer_sup_eq_top S
  intro a ha
  have hmem : (⟨a, ha⟩ : ↥A) ∈
      (Subgroup.normalizer ((S : Subgroup ↥N).map N.subtype : Set ↥A)) ⊔ N := by
    rw [hF]; trivial
  have hle : Subgroup.normalizer ((S : Subgroup ↥N).map N.subtype : Set ↥A) ≤
      Subgroup.normalizer (N : Set ↥A) := by
    rw [(Subgroup.normalizer_eq_top_iff (H := N)).2 inferInstance]; exact le_top
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hmem
  obtain ⟨k, hk, n, hn, hkn⟩ := hmem
  have hSeq : (S : Subgroup ↥N).map N.subtype = P.subgroupOf A := by
    have : (S : Subgroup ↥N) = P₁ := rfl
    rw [this, hP₁]
    exact Subgroup.map_subgroupOf_eq_of_le (fun x hx => by
      exact Subgroup.mem_subgroupOf.2 (hPY hx))
  have hkP : (k : Ω) ∈ Subgroup.normalizer (P : Set Ω) := by
    have hk' : k ∈ Subgroup.normalizer ((P.subgroupOf A : Subgroup ↥A) : Set ↥A) := by
      rw [← hSeq]; exact hk
    rw [← Subgroup.subgroupOf_normalizer_eq (hPY.trans hYA)] at hk'
    exact hk'
  have hy : k * n * k⁻¹ ∈ N := ‹N.Normal›.conj_mem n hn k
  refine ⟨((k * n * k⁻¹ : ↥A) : Ω), Subgroup.mem_subgroupOf.1 hy, (k : Ω), ⟨k.2, hkP⟩, ?_⟩
  have := congrArg Subtype.val hkn
  simp only [Subgroup.coe_mul] at this ⊢
  simp [mul_assoc, ← this]

section Baum

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem thompsonJ_le_baum (T : Subgroup G) : thompsonJ T ≤ baum T := by
  refine le_inf (CFSG.Quasithin.B6.thompsonJ_le T) fun j hj => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have := (C1GN.omegaOneCenterOf_le_centerOf (thompsonJ T) he).2
  exact (Subgroup.mem_centralizer_iff.1 this j hj).symm

theorem normalizer_inf_sup_le_normalizer_baum (T Y : Subgroup G) :
    Subgroup.normalizer ((T ⊓ (baum T ⊔ Y) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (baum T : Set G) := by
  set S : Subgroup G := T ⊓ (baum T ⊔ Y) with hS
  have hBS : baum T ≤ S := le_inf (C1GN.baum_le T) le_sup_left
  have hST : S ≤ T := inf_le_left
  have hJS : thompsonJ T ≤ S := (thompsonJ_le_baum T).trans hBS
  have hJeq : thompsonJ S = thompsonJ T :=
    (CFSG.Quasithin.thompsonJ_eq_of_le (S := T) (R := S) hJS hST).symm
  have hbaum : baum S = baum T := by
    unfold baum
    rw [hJeq]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxS, hxC⟩
      exact ⟨hST hxS, hxC⟩
    · rintro ⟨hxT, hxC⟩
      have hxB : x ∈ baum T := ⟨hxT, hxC⟩
      exact ⟨hBS hxB, hxC⟩
  have := normalizer_le_normalizer_baum S
  rwa [hbaum] at this

end Baum

section Lifting

variable {G : Type} [Group G] [Finite G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}
  {hMN : M ≤ Subgroup.normalizer (V : Set G)}

omit [Finite G] in
theorem mem_sup_of_actM_mem_autI {K : Subgroup G} (hKM : K ≤ M) {m : G} (hm : m ∈ M)
    (h : actM hU hMN ⟨m, hm⟩ ∈ autI hU K) :
    m ∈ K ⊔ (Subgroup.centralizer (V : Set G) ⊓ M) := by
  obtain ⟨g, hgK, hg⟩ := (mem_autI hU).1 h
  rw [actM_eq_convI] at hg
  have hgM : (g : G) ∈ M := hKM hgK
  have h1 : convI hU (g⁻¹ * ⟨m, hMN hm⟩) = 1 := by
    rw [map_mul, map_inv, hg, inv_mul_cancel]
  have h2 : ((g⁻¹ * ⟨m, hMN hm⟩ : Subgroup.normalizer (V : Set G)) : G) ∈
      Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hU _).1 h1
  have h3 : (g : G)⁻¹ * m ∈ Subgroup.centralizer (V : Set G) ⊓ M :=
    ⟨h2, M.mul_mem (M.inv_mem hgM) hm⟩
  have : m = (g : G) * ((g : G)⁻¹ * m) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hgK h3

omit [Finite G] in
theorem autI_thompsonJ_normalized :
    ∀ g ∈ autI hU M, ∀ φ ∈ autI hU (thompsonJ M), g * φ * g⁻¹ ∈ autI hU (thompsonJ M) := by
  intro g hg φ hφ
  obtain ⟨m, hmM, rfl⟩ := (mem_autI hU).1 hg
  obtain ⟨j, hjJ, rfl⟩ := (mem_autI hU).1 hφ
  have hmn : (m : G) ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hmM
  have hmj : (m : G) * (j : G) * (m : G)⁻¹ ∈ thompsonJ M := by
    have h := cjSub_thompsonJ (S := M) (g := (m : G)⁻¹) (inv_mem hmn)
    have : (j : G) ∈ cjSub (m : G)⁻¹ (thompsonJ M) := by rw [h]; exact hjJ
    rw [mem_cjSub] at this
    simpa using this
  have hmjN : (m : G) * (j : G) * (m : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ m.2 j.2) (Subgroup.inv_mem _ m.2)
  rw [mem_autI]
  refine ⟨⟨_, hmjN⟩, hmj, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl


theorem S3Family.exists_split {W : Type*} [CommGroup W] {I : Finset (Subgroup (MulAut W))}
    (hI : S3Family I) (p : Subgroup (MulAut W) → Prop) {y : MulAut W}
    (hy : y ∈ ⨆ L ∈ I, L) :
    ∃ a ∈ ⨆ L ∈ I, ⨆ (_ : p L), L, ∃ b ∈ ⨆ L ∈ I, ⨆ (_ : ¬ p L), L, y = a * b := by
  set A : Subgroup (MulAut W) := ⨆ L ∈ I, ⨆ (_ : p L), L with hA
  set B : Subgroup (MulAut W) := ⨆ L ∈ I, ⨆ (_ : ¬ p L), L with hB
  have hAB : (⨆ L ∈ I, L) ≤ A ⊔ B := by
    refine iSup₂_le fun L hL => ?_
    by_cases h : p L
    · exact le_sup_of_le_left (le_iSup₂_of_le L hL (le_iSup (fun _ : p L => L) h))
    · exact le_sup_of_le_right (le_iSup₂_of_le L hL (le_iSup (fun _ : ¬ p L => L) h))
  have hLB : ∀ L ∈ I, p L → B ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    intro L hL hpL
    refine iSup₂_le fun L' hL' => iSup_le fun hpL' => ?_
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hI.comm L' hL' L hL (fun h => hpL' (h ▸ hpL)) b hb a ha).symm
  have hAc : A ≤ Subgroup.centralizer (B : Set (MulAut W)) := by
    refine iSup₂_le fun L hL => iSup_le fun hpL => ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have := Subgroup.mem_centralizer_iff.1 (hLB L hL hpL hb) a ha
    exact this.symm
  have hAn : A ≤ Subgroup.normalizer (B : Set (MulAut W)) :=
    hAc.trans (Subgroup.centralizer_le_normalizer _)
  have := hAB hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B hAn] at this
  obtain ⟨a, ha, b, hb, rfl⟩ := this
  exact ⟨a, ha, b, hb, rfl⟩

theorem exists_factor_of_covering (hMN : M ≤ Subgroup.normalizer (V : Set G)) {T X : Subgroup G}
    (hT : IsSylowTwoOf T M) (hXT : X ≤ T) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hNS : Subgroup.normalizer ((T ⊓ (X ⊔ Subgroup.centralizer (V : Set G) ⊓ M) : Subgroup G) :
      Set G) ≤ Subgroup.normalizer (X : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hSylJ : IsSylowTwoOf (autI hU X) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L) {KA KB : Subgroup G} (hKA : KA ≤ M)
    (hKB : KB ≤ M) (hcov : ∀ L ∈ I, L ≤ autI hU KA ∨ L ≤ autI hU KB) :
    ∀ m ∈ M, ∃ c ∈ Subgroup.centralizer (V : Set G) ⊓ M, ∃ a ∈ KA, ∃ b ∈ KB,
      ∃ n ∈ M ⊓ Subgroup.normalizer (X : Set G), m = c * a * b * n := by
  intro m hm
  set CM : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ M with hCM
  have hCMn : M ≤ Subgroup.normalizer (CM : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).1
      (centralizer_inf_subgroupOf_normal hU hMN)
  have hCMconj : ∀ g ∈ M, ∀ c ∈ CM, g * c * g⁻¹ ∈ CM := fun g hg c hc =>
    (Subgroup.mem_normalizer_iff.1 (hCMn hg) c).1 hc
  have hJM' : thompsonJ M ≤ M := (CFSG.Quasithin.B6.thompsonJ_le M)
  have hJTM : X ≤ M := hXT.trans hT.1
  have hYA : autI hU (thompsonJ M) ≤ autI hU M := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 hφ
    exact (mem_autI hU).2 ⟨g, hJM' hg, rfl⟩
  have hYn : autI hU M ≤ Subgroup.normalizer (autI hU (thompsonJ M) : Set (MulAut (IntMod V hU))) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro φ
    refine ⟨fun h => autI_thompsonJ_normalized g hg φ h, fun h => ?_⟩
    have := autI_thompsonJ_normalized g⁻¹ ((autI hU M).inv_mem hg) _ h
    simpa [mul_assoc] using this
  have hmA : actM hU hMN ⟨m, hm⟩ ∈ autI hU M := (mem_autI hU).2 ⟨⟨m, hMN hm⟩, hm, rfl⟩
  obtain ⟨y, hyY, n, ⟨hnA, hnP⟩, hmn⟩ := frattini_amb hYA hYn hSylJ _ hmA
  obtain ⟨g, hgM, hg⟩ := (mem_autI hU).1 hnA
  have hgn : actM hU hMN ⟨(g : G), hgM⟩ = n := by rw [actM_eq_convI]; exact hg
  have key : ∀ g' (hg' : g' ∈ M), actM hU hMN ⟨g', hg'⟩ ∈
      Subgroup.normalizer (autI hU X : Set (MulAut (IntMod V hU))) →
      ∀ x ∈ X ⊔ CM, g' * x * g'⁻¹ ∈ X ⊔ CM := by
    intro g' hg' hn x hx
    have hxM : x ∈ M := sup_le hJTM inf_le_right hx
    have hxA : actM hU hMN ⟨x, hxM⟩ ∈ autI hU X := by
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (hJTM.trans hCMn)] at hx
      obtain ⟨j, hj, c, hc, rfl⟩ := hx
      have hc1 : actM hU hMN ⟨c, hc.2⟩ = 1 := (actM_eq_one_iff hU hMN _).2 hc.1
      have : actM hU hMN ⟨j * c, M.mul_mem (hJTM hj) hc.2⟩ = actM hU hMN ⟨j, hJTM hj⟩ := by
        rw [show (⟨j * c, M.mul_mem (hJTM hj) hc.2⟩ : ↥M) = ⟨j, hJTM hj⟩ * ⟨c, hc.2⟩ from rfl,
          map_mul, hc1, mul_one]
      rw [this, actM_eq_convI]
      exact convI_mem_autI hU hj _
    have hgxM : g' * x * g'⁻¹ ∈ M := M.mul_mem (M.mul_mem hg' hxM) (M.inv_mem hg')
    have himg : actM hU hMN ⟨g' * x * g'⁻¹, hgxM⟩ =
        actM hU hMN ⟨g', hg'⟩ * actM hU hMN ⟨x, hxM⟩ * (actM hU hMN ⟨g', hg'⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    have hin : actM hU hMN ⟨g' * x * g'⁻¹, hgxM⟩ ∈ autI hU X := by
      rw [himg]; exact (Subgroup.mem_normalizer_iff.1 hn _).1 hxA
    exact mem_sup_of_actM_mem_autI hJTM hgxM hin
  have hgnorm : (g : G) ∈ Subgroup.normalizer ((X ⊔ CM : Subgroup G) : Set G) := by
    have hPn : ∀ g' (hg' : g' ∈ M), actM hU hMN ⟨g', hg'⟩ ∈
        Subgroup.normalizer (autI hU X : Set (MulAut (IntMod V hU))) →
        actM hU hMN ⟨g'⁻¹, M.inv_mem hg'⟩ ∈
        Subgroup.normalizer (autI hU X : Set (MulAut (IntMod V hU))) := by
      intro g' hg' hn
      have : actM hU hMN ⟨g'⁻¹, M.inv_mem hg'⟩ = (actM hU hMN ⟨g', hg'⟩)⁻¹ := by
        rw [← map_inv]; rfl
      rw [this]; exact Subgroup.inv_mem _ hn
    have hn' : actM hU hMN ⟨(g : G), hgM⟩ ∈
        Subgroup.normalizer (autI hU X : Set (MulAut (IntMod V hU))) := by
      rw [hgn]; exact hnP
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key _ hgM hn' x, fun h => ?_⟩
    have := key _ (M.inv_mem hgM) (hPn _ hgM hn') _ h
    simpa [mul_assoc] using this
  obtain ⟨c₂, hc₂, n₀, hn₀, hgc⟩ := OrdinaryProofs.exists_mul_of_mem_normalizer_sup
    inf_le_right hCMn hT hXT hTX hNS hgM hgnorm
  obtain ⟨a, ha, b, hb, hyab⟩ := hI.exists_split (fun L => L ≤ autI hU KA) (hJM ▸ hyY)
  have haKA : a ∈ autI hU KA := by
    refine (iSup₂_le fun L hL => iSup_le fun hLA => hLA : (⨆ L ∈ I, ⨆ (_ : L ≤ autI hU KA), L) ≤
      autI hU KA) ha
  have hbKB : b ∈ autI hU KB := by
    refine (iSup₂_le fun L hL => iSup_le fun hLA => ?_ : (⨆ L ∈ I, ⨆ (_ : ¬ L ≤ autI hU KA), L) ≤
      autI hU KB) hb
    exact (hcov L hL).resolve_left hLA
  obtain ⟨a', ha'K, ha'⟩ := (mem_autI hU).1 haKA
  obtain ⟨b', hb'K, hb'⟩ := (mem_autI hU).1 hbKB
  have ha₀M : (a' : G) ∈ M := hKA ha'K
  have hb₀M : (b' : G) ∈ M := hKB hb'K
  have hac : actM hU hMN ⟨(a' : G), ha₀M⟩ = a := by rw [actM_eq_convI]; exact ha'
  have hbc : actM hU hMN ⟨(b' : G), hb₀M⟩ = b := by rw [actM_eq_convI]; exact hb'
  have hu : (m : G) * (g : G)⁻¹ ∈ M := M.mul_mem hm (M.inv_mem hgM)
  have hv : (a' : G) * (b' : G) ∈ M := M.mul_mem ha₀M hb₀M
  set c₁ : G := (m : G) * (g : G)⁻¹ * ((a' : G) * (b' : G))⁻¹ with hc₁
  have hc₁M : c₁ ∈ M := M.mul_mem hu (M.inv_mem hv)
  have hc₁CM : c₁ ∈ CM := by
    refine ⟨?_, hc₁M⟩
    refine (actM_eq_one_iff hU hMN ⟨c₁, hc₁M⟩).1 ?_
    have e0 : (⟨c₁, hc₁M⟩ : ↥M) = ⟨m, hm⟩ * (⟨(g : G), hgM⟩ : ↥M)⁻¹ *
        ((⟨(a' : G), ha₀M⟩ : ↥M) * ⟨(b' : G), hb₀M⟩)⁻¹ := rfl
    have e1 : actM hU hMN ⟨c₁, hc₁M⟩ = actM hU hMN ⟨m, hm⟩ * (actM hU hMN ⟨(g : G), hgM⟩)⁻¹ *
        (actM hU hMN ⟨(a' : G), ha₀M⟩ * actM hU hMN ⟨(b' : G), hb₀M⟩)⁻¹ := by
      rw [e0]; simp only [map_mul, map_inv]
    rw [e1, hac, hbc, hgn, hmn, hyab]
    group
  have hm' : (m : G) = c₁ * (a' : G) * (b' : G) * ((c₂ * n₀)) := by
    rw [← hgc, hc₁]; group
  refine ⟨c₁ * ((a' : G) * ((b' : G) * c₂ * (b' : G)⁻¹) * (a' : G)⁻¹), ?_, a', ha'K, b', hb'K, n₀,
    hn₀, ?_⟩
  · have h1 : (b' : G) * c₂ * (b' : G)⁻¹ ∈ CM := hCMconj _ hb₀M _ hc₂
    have h2 : (a' : G) * ((b' : G) * c₂ * (b' : G)⁻¹) * (a' : G)⁻¹ ∈ CM := hCMconj _ ha₀M _ h1
    exact CM.mul_mem hc₁CM h2
  · rw [hm']; group

end Lifting

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
