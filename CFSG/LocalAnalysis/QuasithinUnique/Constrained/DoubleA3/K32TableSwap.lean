module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableA4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32B
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32S

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519

section Normalizers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem k32_le_normalizer_of_index_two {N H : Subgroup G} (hNH : N ≤ H) (h2 : N.relIndex H = 2) :
    H ≤ Subgroup.normalizer (N : Set G) := by
  have hnorm : (N.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two h2
  have key : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    have := hnorm.conj_mem (⟨n, hNH hn⟩ : ↥H) (by simpa [Subgroup.mem_subgroupOf] using hn) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact key g hg n
  · intro hn
    have := key g⁻¹ (H.inv_mem hg) _ hn
    have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
    rwa [e] at this

omit [Finite G] in
theorem k32_le_normalizer_inf_centralizer {L K : Subgroup G}
    (hLK : L ≤ Subgroup.normalizer (K : Set G)) :
    L ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
  have key : ∀ l ∈ L, ∀ h ∈ L ⊓ Subgroup.centralizer (K : Set G),
      l * h * l⁻¹ ∈ L ⊓ Subgroup.centralizer (K : Set G) := by
    intro l hl h hh
    refine ⟨L.mul_mem (L.mul_mem hl hh.1) (L.inv_mem hl), ?_⟩
    show l * h * l⁻¹ ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : l⁻¹ * k * l ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hLK (L.inv_mem hl)) k).mp hk
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hh.2 _ hk'
    calc k * (l * h * l⁻¹) = l * ((l⁻¹ * k * l) * h) * l⁻¹ := by group
      _ = l * (h * (l⁻¹ * k * l)) * l⁻¹ := by rw [hc]
      _ = (l * h * l⁻¹) * k := by group
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key l hl h
  · intro hh
    have := key l⁻¹ (L.inv_mem hl) _ hh
    have e : l⁻¹ * (l * h * l⁻¹) * l⁻¹⁻¹ = h := by group
    rwa [e] at this

theorem k32_inf_centralizer_eq_bot {L K : Subgroup G} {z₁ : G} (hA : IsA4Block L (blockU L))
    (hz₁ : z₁ ∈ blockU L) (hLK : L ≤ Subgroup.normalizer (K : Set G))
    (hnc : ¬ ∀ k ∈ K, k * z₁ = z₁ * k) : L ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  by_contra hne
  have hU := k32_le_of_normal_ne_bot hA inf_le_left (k32_le_normalizer_inf_centralizer hLK) hne
  have hz₁C : z₁ ∈ L ⊓ Subgroup.centralizer (K : Set G) := hU hz₁
  exact hnc fun k hk => Subgroup.mem_centralizer_iff.mp hz₁C.2 k hk

end Normalizers

section Swapped

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem k32_false_of_swapped (hP : Prop121Three) (hD : AppC.C56DoubleA3)
    (h27_1 : Lemma2_4_27_1A3) (hAlt : K32AltOut) (ctx : K32Ctx T M H S L s x z₁ z₂ K)
    (hS : ¬ sOne S x ≤ Subgroup.normalizer (K : Set G)) : False := by
  classical
  have hcs := ctx.a3.cs
  have h3 := ctx.a3.a3
  have hB31 := basic31 hD h27_1 ctx.a3.toA3A3
  have hA4 : IsA4Block L (blockU L) := IsA4Block.of_alt3 hcs.block.1.1 h3
  have hz₁U : z₁ ∈ blockU L := ctx.a3.z₁_mem.1
  have hz₁L : z₁ ∈ L := hA4.le hz₁U
  have hLG₂ : L ≤ centralizerElem z₂ := ctx.a3.L_le_cent₂
  have hS₁G₂ : sOne S x ≤ centralizerElem z₂ := ctx.sylow.1
  have hKG₂ : K ≤ centralizerElem z₂ := ctx.comp.1
  have hRL : baum S ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hB31.N_eq]; exact inf_le_right
  have hRidx : (baum S).relIndex (sOne S x) = 2 := A3A3x.relIndex_baum_sOne' hD h27_1 ctx.a3
  obtain ⟨r, hrS₁, hrN⟩ : ∃ r ∈ sOne S x, r ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hS hcon
  have hrG₂ : r ∈ centralizerElem z₂ := hS₁G₂ hrS₁
  have hrz₂ : r⁻¹ * z₂ * r = z₂ := by
    have h1 : r * z₂ = z₂ * r := Subgroup.mem_centralizer_singleton_iff.mp hrG₂
    calc r⁻¹ * z₂ * r = r⁻¹ * (z₂ * r) := by group
      _ = r⁻¹ * (r * z₂) := by rw [h1]
      _ = z₂ := by group
  have hrz₁ : r * z₁ * r⁻¹ = z₁ := by
    have h1 : r * z₁ = z₁ * r := sOne_comm_z₁ ctx.a3 hrS₁
    calc r * z₁ * r⁻¹ = (z₁ * r) * r⁻¹ := by rw [h1]
      _ = z₁ := by group
  have hs := hcs.setting
  have hpc : pCoreOf 2 (centralizerElem z₂) ≠ ⊥ :=
    pCoreOf_centralizerElem_ne_bot ctx.a3.z₂_ne ctx.a3.sq₂
  have hJc : K ∈ cComp (centralizerElem z₂) := mem_cComp_of_isComponentIn ctx.comp
  have hidx2 : (centralizerElem z₂ ⊓ Subgroup.normalizer (K : Set G)).relIndex
      (centralizerElem z₂) = 2 := by
    rcases hP G hs.simple hs.nonabelian hs.qtke _ hpc K hJc with hnorm | ⟨hcard, -⟩
    · exact absurd (hS₁G₂.trans hnorm) hS
    · rw [← card_conj_orbit_eq_relIndex]; exact hcard
  set N : Subgroup G := centralizerElem z₂ ⊓ Subgroup.normalizer (K : Set G) with hNdef
  have hNG₂ : N ≤ centralizerElem z₂ := inf_le_left
  have hNK : N ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  have hKN : K ≤ N := le_inf hKG₂ Subgroup.le_normalizer
  have hG₂N : centralizerElem z₂ ≤ Subgroup.normalizer (N : Set G) :=
    k32_le_normalizer_of_index_two hNG₂ hidx2
  have hLN : L ≤ N := by
    have hM₀ : L ⊓ N = L := by
      refine k32_eq_of_relIndex_le_two hA4 inf_le_left ?_ ?_
      · intro l hl
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 := Subgroup.mem_normalizer_iff.mp (hG₂N (hLG₂ hl)) y
        have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hl) y
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨hy1, hy2⟩
          exact ⟨h2.mp hy1, h1.mp hy2⟩
        · rintro ⟨hy1, hy2⟩
          exact ⟨h2.mpr hy1, h1.mpr hy2⟩
      · have e : (L ⊓ N).relIndex L = N.relIndex L := by
          rw [inf_comm]; exact Subgroup.inf_relIndex_right N L
        rw [e]
        have := Subgroup.relIndex_le_of_le_right hLG₂ (H := N) (by rw [hidx2]; norm_num)
        omega
    exact hM₀ ▸ inf_le_right
  set K' : Subgroup G := conjR K r with hK'def
  have hK'comp : IsComponentIn K' (centralizerElem z₂) :=
    isComponentIn_conj_cent r hrz₂ ctx.comp
  have hK'ne : K' ≠ K := fun h => hrN (mem_normalizer_iff_conjR_eq.mpr h)
  have hKK' : ⁅K, K'⁆ = ⊥ := by
    rcases BenderBranch.eq_or_commute_of_isComponentIn ctx.comp hK'comp with h | h
    · exact absurd h.symm hK'ne
    · exact h
  have hKC' : K ≤ Subgroup.centralizer (K' : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKK'
  have hNK' : N ≤ Subgroup.normalizer (K' : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_conjR_eq, hK'def]
    have hrgr : r * g * r⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hG₂N hrG₂) g).mp hg
    have h1 : conjR K (r * g * r⁻¹) = K := mem_normalizer_iff_conjR_eq.mp (hNK hrgr)
    calc conjR (conjR K r) g = conjR K (r * g) := conjR_conjR_eq K r g
      _ = conjR K ((r * g * r⁻¹) * r) := by congr 1; group
      _ = conjR (conjR K (r * g * r⁻¹)) r := (conjR_conjR_eq K _ r).symm
      _ = conjR K r := by rw [h1]
  have hnc : ¬ ∀ k ∈ K, k * z₁ = z₁ * k := k32_z₁_not_central ctx
  have hCK : L ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
    k32_inf_centralizer_eq_bot hA4 hz₁U (hLN.trans hNK) hnc
  have hnc' : ¬ ∀ k ∈ K', k * z₁ = z₁ * k := by
    intro h
    apply hnc
    intro k hk
    have hk' : r⁻¹ * k * r ∈ K' := by
      rw [hK'def, mem_conjR]
      have e : r * (r⁻¹ * k * r) * r⁻¹ = k := by group
      rw [e]; exact hk
    have h1 := h _ hk'
    calc k * z₁ = k * (r * z₁ * r⁻¹) := by rw [hrz₁]
      _ = r * ((r⁻¹ * k * r) * z₁) * r⁻¹ := by group
      _ = r * (z₁ * (r⁻¹ * k * r)) * r⁻¹ := by rw [h1]
      _ = (r * z₁ * r⁻¹) * k := by group
      _ = z₁ * k := by rw [hrz₁]
  have hCK' : L ⊓ Subgroup.centralizer (K' : Set G) = ⊥ :=
    k32_inf_centralizer_eq_bot hA4 hz₁U (hLN.trans hNK') hnc'
  have hPK : IsSylowTwoOf (sOne S x ⊓ K) K := by
    have h1 : IsSylowTwoOf (sOne S x ⊓ N) N := A4.isSylowTwoOf_inf_normal ctx.sylow hNG₂ hG₂N
    have h2 : IsSylowTwoOf ((sOne S x ⊓ N) ⊓ K) K := A4.isSylowTwoOf_inf_normal h1 hKN hNK
    have e : (sOne S x ⊓ N) ⊓ K = sOne S x ⊓ K := by
      ext y
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hKN h.2⟩, h.2⟩⟩
    rwa [e] at h2
  set PK : Subgroup G := sOne S x ⊓ K with hPKdef
  have hPKK : PK ≤ K := inf_le_right
  set W₀ : Subgroup G := PK ⊓ Subgroup.centralizer (L : Set G) with hW₀def
  have hnormL_cent : PK ⊓ Subgroup.normalizer (L : Set G) ≤ W₀ := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    show p ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hpK : p ∈ K := hp.1.2
    have hpL : p * l * p⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hp.2 l).mp hl
    have hLK' : L ≤ Subgroup.normalizer (K' : Set G) := hLN.trans hNK'
    have hmem : l⁻¹ * (p * l * p⁻¹) ∈ L ⊓ Subgroup.centralizer (K' : Set G) := by
      refine ⟨L.mul_mem (L.inv_mem hl) hpL, ?_⟩
      show l⁻¹ * (p * l * p⁻¹) ∈ Subgroup.centralizer (K' : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy_p : y * p = p * y := Subgroup.mem_centralizer_iff.mp (hKC' hpK) y hy
      have hly : l * y * l⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp (hLK' hl) y).mp hy
      have hy_l : (l * y * l⁻¹) * p = p * (l * y * l⁻¹) :=
        Subgroup.mem_centralizer_iff.mp (hKC' hpK) _ hly
      have hyp' : y * p⁻¹ = p⁻¹ * y := by
        calc y * p⁻¹ = p⁻¹ * (p * y) * p⁻¹ := by group
          _ = p⁻¹ * (y * p) * p⁻¹ := by rw [hy_p]
          _ = p⁻¹ * y := by group
      calc y * (l⁻¹ * (p * l * p⁻¹)) = l⁻¹ * ((l * y * l⁻¹) * p) * l * p⁻¹ := by group
        _ = l⁻¹ * (p * (l * y * l⁻¹)) * l * p⁻¹ := by rw [hy_l]
        _ = l⁻¹ * p * l * (y * p⁻¹) := by group
        _ = l⁻¹ * p * l * (p⁻¹ * y) := by rw [hyp']
        _ = (l⁻¹ * (p * l * p⁻¹)) * y := by group
    rw [hCK'] at hmem
    have h1 : l⁻¹ * (p * l * p⁻¹) = 1 := Subgroup.mem_bot.mp hmem
    have h2 : p * l * p⁻¹ = l := by
      calc p * l * p⁻¹ = l * (l⁻¹ * (p * l * p⁻¹)) := by group
        _ = l := by rw [h1]; group
    have h3 : p * l = l * p := by
      calc p * l = (p * l * p⁻¹) * p := by group
        _ = l * p := by rw [h2]
    exact h3.symm
  have hW₀idx : W₀.relIndex PK ≤ 2 := by
    have hsub : PK ⊓ baum S ≤ W₀ := fun y hy => hnormL_cent ⟨hy.1, hRL hy.2⟩
    have h1 : W₀.relIndex PK ≤ (PK ⊓ baum S).relIndex PK :=
      Subgroup.relIndex_le_of_le_left hsub Subgroup.index_ne_zero_of_finite
    have h2 : (PK ⊓ baum S).relIndex PK = (baum S).relIndex PK :=
      Subgroup.inf_relIndex_left PK (baum S)
    have h3 : (baum S).relIndex PK ≤ (baum S).relIndex (sOne S x) :=
      Subgroup.relIndex_le_of_le_right (inf_le_left : PK ≤ sOne S x) (by rw [hRidx]; norm_num)
    omega
  set φ := k32ActHom K N hNK with hφ
  let f₀ : ↥L →* MulAut ↥K := φ.comp (Subgroup.inclusion hLN)
  have hf₀apply : ∀ (l : ↥L) (y : ↥K), ((f₀ l y : ↥K) : G) = (l : G) * y * (l : G)⁻¹ :=
    fun l y => rfl
  have hf₀inj : Function.Injective f₀ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : (a : G) ∈ Subgroup.centralizer (K : Set G) :=
      (k32ActHom_eq_one_iff K N hNK (Subgroup.inclusion hLN a)).mp ha
    have hmem : (a : G) ∈ L ⊓ Subgroup.centralizer (K : Set G) := ⟨a.2, hc⟩
    rw [hCK] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hA' : IsA4Block f₀.range (((blockU L).subgroupOf L).map f₀) :=
    k32_isA4Block_range hA4 f₀ hf₀inj
  set V : Subgroup (MulAut ↥K) := ((blockU L).subgroupOf L).map f₀ with hVdef
  set J : Subgroup (MulAut ↥K) := innAut ↥K with hJdef
  have hAJ : f₀.range ≤ Subgroup.normalizer (J : Set (MulAut ↥K)) := by
    have : J.Normal := innAut_normal ↥K
    rw [Subgroup.normalizer_eq_top J]
    exact le_top
  let a₁ : ↥L := ⟨z₁, hz₁L⟩
  have hv₁V : f₀ a₁ ∈ V := ⟨a₁, by simpa [Subgroup.mem_subgroupOf] using hz₁U, rfl⟩
  have hv₁ne : f₀ a₁ ≠ 1 := by
    intro h
    have := hf₀inj (h.trans (map_one f₀).symm)
    exact ctx.a3.z₁_ne (congrArg Subtype.val this)
  have hVJ : V ≤ J := by
    obtain ⟨v, hvV, hvJ, hv1⟩ : ∃ v ∈ V, v ∈ J ∧ v ≠ 1 := by
      by_cases hq : CentralQuotientAlt K 6 ∨ CentralQuotientAlt K 7
      · have hne : V ⊓ innAut ↥K ≠ ⊥ :=
          hAlt ↥K (BenderBranch.isQuasisimple_of_isComponentIn ctx.comp) hq _ V hA'
        by_contra hcon
        push Not at hcon
        apply hne
        rw [eq_bot_iff]
        intro v hv
        rw [Subgroup.mem_bot]
        exact hcon v hv.1 hv.2
      · obtain ⟨hn6, hn7⟩ := not_or.mp hq
        refine ⟨f₀ a₁, hv₁V, ?_, hv₁ne⟩
        obtain ⟨l, hlK, hl⟩ := ctx.inner ⟨hn6, hn7⟩
        refine ⟨⟨l⁻¹, K.inv_mem hlK⟩, ?_⟩
        ext y
        have hz₁inv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ctx.a3.sq₁)
        have hy := hl y y.2
        have hy₁K : z₁ * (y : G) * z₁⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hNK (hLN hz₁L)) y).mp y.2
        have hz₂c : (z₁ * (y : G) * z₁⁻¹) * z₂ = z₂ * (z₁ * (y : G) * z₁⁻¹) :=
          Subgroup.mem_centralizer_singleton_iff.mp (hKG₂ hy₁K)
        have hcalc : (z₁ * z₂)⁻¹ * (y : G) * (z₁ * z₂) = z₁ * (y : G) * z₁⁻¹ := by
          calc (z₁ * z₂)⁻¹ * (y : G) * (z₁ * z₂) = z₂⁻¹ * (z₁⁻¹ * (y : G) * z₁) * z₂ := by group
            _ = z₂⁻¹ * (z₁ * (y : G) * z₁⁻¹) * z₂ := by rw [hz₁inv]
            _ = z₂⁻¹ * ((z₁ * (y : G) * z₁⁻¹) * z₂) := by group
            _ = z₂⁻¹ * (z₂ * (z₁ * (y : G) * z₁⁻¹)) := by rw [hz₂c]
            _ = z₁ * (y : G) * z₁⁻¹ := by group
        have hgoal : ((MulAut.conj (⟨l⁻¹, K.inv_mem hlK⟩ : ↥K) y : ↥K) : G) = l⁻¹ * (y : G) * l := by
          simp [MulAut.conj_apply]
        have hgoal2 : ((f₀ a₁ y : ↥K) : G) = z₁ * (y : G) * z₁⁻¹ := rfl
        rw [hgoal, hgoal2, ← hcalc]
        exact hy.symm
    exact hA'.le_of_mem hAJ hvJ hvV hv1
  let c : ↥K →* MulAut ↥K := MulAut.conj
  have hPsyl : IsSylowTwoOf ((PK.subgroupOf K).map c) J := k32_isSylowTwoOf_map c hPK
  have hsub : W₀.subgroupOf K ≤ PK.subgroupOf K := fun a ha =>
    Subgroup.mem_subgroupOf.mpr ((inf_le_left : W₀ ≤ PK) (Subgroup.mem_subgroupOf.mp ha))
  have hWP : (W₀.subgroupOf K).map c ≤ (PK.subgroupOf K).map c := Subgroup.map_mono hsub
  have hcapply : ∀ (w y : ↥K), ((c w y : ↥K) : G) = (w : G) * y * (w : G)⁻¹ := fun w y => by
    simp [c, MulAut.conj_apply]
  have hWC : (W₀.subgroupOf K).map c ≤ Subgroup.centralizer (f₀.range : Set (MulAut ↥K)) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, rfl⟩
    have hwL : ∀ l' ∈ L, l' * (w : G) = (w : G) * l' := fun l' hl' =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hw).2 l' hl'
    ext y
    rw [MulAut.mul_apply, MulAut.mul_apply, hf₀apply, hcapply, hcapply, hf₀apply]
    have h1 : (l : G) * (w : G) = (w : G) * (l : G) := hwL l l.2
    calc (l : G) * ((w : G) * (y : G) * (w : G)⁻¹) * (l : G)⁻¹
        = ((l : G) * (w : G)) * (y : G) * ((l : G) * (w : G))⁻¹ := by group
      _ = ((w : G) * (l : G)) * (y : G) * ((w : G) * (l : G))⁻¹ := by rw [h1]
      _ = (w : G) * ((l : G) * (y : G) * (l : G)⁻¹) * (w : G)⁻¹ := by group
  have hWidx : ((W₀.subgroupOf K).map c).relIndex ((PK.subgroupOf K).map c) ≤ 2 := by
    have h1 := k32_relIndex_map_dvd c hsub
    have h2 : (W₀.subgroupOf K).relIndex (PK.subgroupOf K) = W₀.relIndex PK :=
      Subgroup.relIndex_subgroupOf hPKK
    rw [h2] at h1
    have h0 : W₀.relIndex PK ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h1
    omega
  exact false_of_centralizer_index_le_two hA' hVJ hPsyl hWP hWC hWidx

end Swapped

end CFSG.QuasithinUnique.DoubleA3
