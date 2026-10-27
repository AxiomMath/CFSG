module

public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

@[expose] def preCentralizer (N K : Subgroup G) : Subgroup G :=
  ((Subgroup.centralizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N))).comap
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).map N.subtype

omit [Finite G] in
theorem preCentralizer_le (N K : Subgroup G) : preCentralizer N K ≤ N :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem glaPPrimeCoreOf_le_preCentralizer (N K : Subgroup G) :
    GLAPPrimeCoreOf 3 N ≤ preCentralizer N K := by
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨n, Subgroup.mem_comap.2 ?_, rfl⟩
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
  rw [h1]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem mem_preCentralizer_iff {N K : Subgroup G} {x : G} :
    x ∈ preCentralizer N K ↔ ∃ hx : x ∈ N, QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨x, hx⟩ ∈
      Subgroup.centralizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [Finite G] in
theorem mem_glaPPrimeCore_of_mem {N : Subgroup G} {x : ↥N}
    (h : (x : G) ∈ GLAPPrimeCoreOf 3 N) : x ∈ GLAPPrimeCore 3 ↥N := by
  obtain ⟨x', hx', hxx⟩ := h
  have : x' = x := Subtype.ext hxx
  subst this
  exact hx'

omit [Finite G] in
theorem mk_comm_of_commutator_mem {N : Subgroup G} {x y : ↥N}
    (h : ((x * y * x⁻¹ * y⁻¹ : ↥N) : G) ∈ GLAPPrimeCoreOf 3 N) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) x * QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) y =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) y * QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) x := by
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) (x * y * x⁻¹ * y⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (mem_glaPPrimeCore_of_mem h)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  set a := QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) x
  set b := QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) y
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

omit [Finite G] in
theorem le_normalizer_preCentralizer {B N K : Subgroup G} (hBN : B ≤ N)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) :
    B ≤ Subgroup.normalizer (preCentralizer N K : Set G) := by
  intro b hb
  have hbar : barX 3 N B ≤ Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    barX_le_normalizer hBK
  have hb' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨b, hBN hb⟩ ∈
      Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    hbar ⟨⟨b, hBN hb⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) with hπ
  have key : ∀ (u : ↥N ⧸ GLAPPrimeCore 3 ↥N),
      u ∈ Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) →
      ∀ c ∈ Subgroup.centralizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)),
        u * c * u⁻¹ ∈ Subgroup.centralizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
    intro u hu c hc
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : u⁻¹ * z * u ∈ barX 3 N K := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hu) z).1 hz
      simpa using this
    have := Subgroup.mem_centralizer_iff.1 hc _ hz'
    calc z * (u * c * u⁻¹) = u * ((u⁻¹ * z * u) * c) * u⁻¹ := by group
      _ = u * (c * (u⁻¹ * z * u)) * u⁻¹ := by rw [this]
      _ = (u * c * u⁻¹) * z := by group
  rw [Subgroup.mem_normalizer_iff]
  have one_way : ∀ {u : G} (hu : u ∈ B) (x : G),
      x ∈ preCentralizer N K → u * x * u⁻¹ ∈ preCentralizer N K := by
    intro u hu x hx
    obtain ⟨hxN, hxc⟩ := mem_preCentralizer_iff.1 hx
    have hnorm : π ⟨u, hBN hu⟩ ∈
        Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
      hbar ⟨⟨u, hBN hu⟩, (Subgroup.mem_subgroupOf).2 hu, rfl⟩
    have huN : u * x * u⁻¹ ∈ N := N.mul_mem (N.mul_mem (hBN hu) hxN) (N.inv_mem (hBN hu))
    refine mem_preCentralizer_iff.2 ⟨huN, ?_⟩
    have e : (⟨u * x * u⁻¹, huN⟩ : ↥N) = ⟨u, hBN hu⟩ * ⟨x, hxN⟩ * ⟨u, hBN hu⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact key _ hnorm _ hxc
  intro x
  constructor
  · exact one_way hb x
  · intro hx
    have := one_way (B.inv_mem hb) _ hx
    have e : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
    rwa [e] at this

omit [Finite G] in
theorem commutator_mem_of_mem_preCentralizer {N K I : Subgroup G} (hIN : I ≤ N)
    (hI : barX 3 N I ≤ barX 3 N K) {s g : G} (hs : s ∈ preCentralizer N K) (hg : g ∈ I) :
    s * g * s⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 N := by
  obtain ⟨hsN, hsc⟩ := mem_preCentralizer_iff.1 hs
  have hgb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨g, hIN hg⟩ ∈ barX 3 N K :=
    hI ⟨⟨g, hIN hg⟩, (Subgroup.mem_subgroupOf).2 hg, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.1 hsc _ hgb
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)
      (⟨s, hsN⟩ * ⟨g, hIN hg⟩ * ⟨s, hsN⟩⁻¹ * ⟨g, hIN hg⟩⁻¹ : ↥N) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  exact ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

omit [Finite G] in
theorem centralizerQuot_le_preCentralizer {B N K : Subgroup G} (hBN : B ≤ N)
    (hOK : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 N) :
    centralizerQuot B K ≤ preCentralizer N K := by
  refine (Subgroup.closure_le _).2 fun b hbS => ?_
  obtain ⟨hbB, hb⟩ := hbS
  refine mem_preCentralizer_iff.2 ⟨hBN hbB, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : (k : G) ∈ K := (Subgroup.mem_subgroupOf).1 hk
  have h := hOK (hb _ hk')
  refine mk_comm_of_commutator_mem (x := k) (y := ⟨b, hBN hbB⟩) ?_
  have := hb k hk'
  have hinv := (GLAPPrimeCoreOf 3 N).inv_mem (hOK (hb _ hk'))
  convert hinv using 1
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  group

set_option linter.unusedVariables false in
omit [Finite G] in
theorem exists_ne_one_mem_preCentralizer {B N K T : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ N) (hTN : T ≤ N) (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hCT : B ⊓ Subgroup.centralizer (T : Set G) = ⊥) (hB1 : B ≠ ⊥)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hKN : K ≤ N)
    (hOK : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 N)
    (hsup : centralizerQuot B K ⊔ (B ⊓ K) = B)
    (hFT : ∀ f ∈ barX 3 N (B ⊓ K), ∀ t ∈ barX 3 N T, f * t = t * f)
    (hTK : barX 3 N T ≤ Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N))) :
    ∃ y ∈ T ⊓ preCentralizer N K, y ≠ 1 := by
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) with hπ
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hB1 ((Subgroup.eq_bot_iff_forall _).2 hcon)
  obtain ⟨t, ht, hbt⟩ : ∃ t ∈ T, b * t ≠ t * b := by
    by_contra hcon
    push Not at hcon
    have : b ∈ B ⊓ Subgroup.centralizer (T : Set G) :=
      ⟨hb, Subgroup.mem_centralizer_iff.2 fun t ht => (hcon t ht).symm⟩
    rw [hCT, Subgroup.mem_bot] at this
    exact hb1 this
  have hbN : b ∈ N := hBN hb
  have htN : t ∈ N := hTN ht
  have hyT : b * t * b⁻¹ * t⁻¹ ∈ T :=
    T.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBT hb) t).1 ht) (T.inv_mem ht)
  have hyN : b * t * b⁻¹ * t⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem hbN htN) (N.inv_mem hbN)) (N.inv_mem htN)
  refine ⟨b * t * b⁻¹ * t⁻¹, ⟨hyT, ?_⟩, ?_⟩
  swap
  · intro h1
    apply hbt
    have : b * t = t * b := by
      calc b * t = (b * t * b⁻¹ * t⁻¹) * (t * b) := by group
        _ = t * b := by rw [h1, one_mul]
    exact this
  have hAB : centralizerQuot B K ≤ B := (Subgroup.closure_le B).2 fun x hx => hx.1
  have hAc : centralizerQuot B K ≤ Subgroup.centralizer ((B ⊓ K : Subgroup G) : Set G) :=
    fun a ha => Subgroup.mem_centralizer_iff.2 fun f hf =>
      (elemAbelian_comm hBel (hAB ha) hf.1).symm
  obtain ⟨a, ha, f, hf, hbaf⟩ := exists_mul_of_mem_sup hAc (hsup ▸ hb)
  have haN : a ∈ N := hBN (hAB ha)
  have hfN : f ∈ N := hBN hf.1
  have hAcen := (mem_preCentralizer_iff.1
    (centralizerQuot_le_preCentralizer hBN hOK ha)).2
  have hfb : π ⟨f, hfN⟩ ∈ barX 3 N (B ⊓ K) :=
    ⟨⟨f, hfN⟩, (Subgroup.mem_subgroupOf).2 hf, rfl⟩
  have htb : π ⟨t, htN⟩ ∈ barX 3 N T := ⟨⟨t, htN⟩, (Subgroup.mem_subgroupOf).2 ht, rfl⟩
  have hft := hFT _ hfb _ htb
  refine mem_preCentralizer_iff.2 ⟨hyN, ?_⟩
  set ab := π ⟨a, haN⟩
  set fb := π ⟨f, hfN⟩
  set tb := π ⟨t, htN⟩
  have e1 : (⟨b * t * b⁻¹ * t⁻¹, hyN⟩ : ↥N) =
      (⟨a, haN⟩ * ⟨f, hfN⟩) * ⟨t, htN⟩ * (⟨a, haN⟩ * ⟨f, hfN⟩)⁻¹ * ⟨t, htN⟩⁻¹ := by
    apply Subtype.ext
    simp [hbaf]
  have hyb : π ⟨b * t * b⁻¹ * t⁻¹, hyN⟩ = ab * (tb * ab⁻¹ * tb⁻¹) := by
    rw [e1]
    simp only [map_mul, map_inv]
    change ab * fb * tb * (ab * fb)⁻¹ * tb⁻¹ = ab * (tb * ab⁻¹ * tb⁻¹)
    have e2 : fb * tb * fb⁻¹ = tb := by
      rw [hft]; group
    calc ab * fb * tb * (ab * fb)⁻¹ * tb⁻¹ = ab * (fb * tb * fb⁻¹) * ab⁻¹ * tb⁻¹ := by group
      _ = ab * (tb * ab⁻¹ * tb⁻¹) := by rw [e2]; group
  rw [hyb]
  refine Subgroup.mul_mem _ hAcen ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : tb⁻¹ * z * tb ∈ barX 3 N K := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem (hTK htb)) z).1 hz
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.1 ((Subgroup.centralizer _).inv_mem hAcen) _ hz'
  calc z * (tb * ab⁻¹ * tb⁻¹) = tb * ((tb⁻¹ * z * tb) * ab⁻¹) * tb⁻¹ := by group
    _ = tb * (ab⁻¹ * (tb⁻¹ * z * tb)) * tb⁻¹ := by rw [hc]
    _ = (tb * ab⁻¹ * tb⁻¹) * z := by group

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
