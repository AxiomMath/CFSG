module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAut
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentFrattiniTriv
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentKpIrred

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_mul_eq {L : Subgroup G} {l o : G} (hl : l ∈ L)
    (ho : o ∈ Subgroup.normalizer (L : Set G)) (m : ℕ) :
    ∃ l' ∈ L, (l * o) ^ m = l' * o ^ m := by
  induction m with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨l', hl', he⟩ := ih
    have hc : o ^ m * l * (o ^ m)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ho m) l).mp hl
    refine ⟨l' * (o ^ m * l * (o ^ m)⁻¹), L.mul_mem hl' hc, ?_⟩
    rw [pow_succ, he, pow_succ]
    group

section Generic

variable {p : ℕ} [Fact p.Prime] {C : Subgroup G}
  {K : Subgroup (C ⧸ primeComplementCore (G := C) p)} [hK : K.Normal]

local notation "φ" => RankOneSylow.act (primeComplementCore (G := C) p) K

theorem mem_d1PlusCore_of_mem_core {c : C} (hc : c ∈ primeComplementCore (G := C) p) :
    (c : G) ∈ d1PlusCore p C K := by
  rw [mem_d1PlusCore_iff_mem_ker, RankOneSylow.mem_ker_act,
    (QuotientGroup.eq_one_iff c).mpr hc]
  exact Subgroup.one_mem _

theorem mem_core_of_mem_inf (hZ : Subgroup.center ↥K = ⊥) {c : C}
    (hcK : (c : G) ∈ hyp111Pre p C K) (hcX : (c : G) ∈ d1PlusCore p C K) :
    c ∈ primeComplementCore (G := C) p := by
  have hcK' : (c : C ⧸ primeComplementCore (G := C) p) ∈ K := by
    obtain ⟨c', hc', he⟩ := hcK
    rwa [C.subtype_injective he] at hc'
  have h1 := MonoidHom.mem_ker.mp ((mem_d1PlusCore_iff_mem_ker c).mp hcX)
  rw [RankOneSylow.act_eq_conj hcK'] at h1
  have h2 := conj_injective_of_center hZ (h1.trans (map_one _).symm)
  exact (QuotientGroup.eq_one_iff c).mp (congrArg Subtype.val h2)

theorem conj_mem_hyp111Pre {c k : G} (hc : c ∈ C) (hk : k ∈ hyp111Pre p C K) :
    c * k * c⁻¹ ∈ hyp111Pre p C K := by
  obtain ⟨k', hk', rfl⟩ := hk
  exact ⟨⟨c, hc⟩ * k' * ⟨c, hc⟩⁻¹, (hK.comap _).conj_mem k' hk' _, rfl⟩

theorem conj_mem_d1PlusCore {c x : G} (hc : c ∈ C) (hx : x ∈ d1PlusCore p C K) :
    c * x * c⁻¹ ∈ d1PlusCore p C K := by
  have hxC : x ∈ C := Subgroup.map_subtype_le _ hx
  have hx' : (⟨x, hxC⟩ : C) ∈ MonoidHom.ker φ := (mem_d1PlusCore_iff_mem_ker _).mp hx
  exact (mem_d1PlusCore_iff_mem_ker (⟨c, hc⟩ * ⟨x, hxC⟩ * ⟨c, hc⟩⁻¹)).mpr
    ((MonoidHom.normal_ker φ).conj_mem _ hx' _)

theorem comm_mem_of_mem_hyp111Pre (hZ : Subgroup.center ↥K = ⊥) {L M : Subgroup G}
    (hLM : M ≤ Subgroup.normalizer (L : Set G)) (hXM : d1PlusCore p C K ≤ M) {g t w : G}
    (hgK : g ∈ hyp111Pre p C K) (hgM : g ∈ M) (hwC : w ∈ C) (hwL : w ∈ L)
    (hx : w⁻¹ * t ∈ d1PlusCore p C K) (hz : ∃ e : ℕ, (g * t * g⁻¹ * t⁻¹) ^ (p ^ e) = 1) :
    g * t * g⁻¹ * t⁻¹ ∈ L := by
  have hp : p.Prime := Fact.out
  set O := primeComplementCore (G := C) p with hO
  set Ob : Subgroup G := O.map C.subtype with hOb
  set x := w⁻¹ * t with hxdef
  have hxC : x ∈ C := Subgroup.map_subtype_le _ hx
  have hgC : g ∈ C := Subgroup.map_subtype_le _ hgK
  set n := g * x * g⁻¹ * x⁻¹ with hn
  have hnK : n ∈ hyp111Pre p C K := by
    have := (hyp111Pre p C K).mul_mem hgK (conj_mem_hyp111Pre hxC
      ((hyp111Pre p C K).inv_mem hgK))
    simpa [hn, mul_assoc] using this
  have hnX : n ∈ d1PlusCore p C K :=
    (d1PlusCore p C K).mul_mem (conj_mem_d1PlusCore hgC hx) ((d1PlusCore p C K).inv_mem hx)
  have hnC : n ∈ C := Subgroup.map_subtype_le _ hnK
  have hnO : (⟨n, hnC⟩ : C) ∈ O := mem_core_of_mem_inf hZ hnK hnX
  set o := w * n * w⁻¹ with ho
  have hoO : o ∈ Ob :=
    ⟨⟨w, hwC⟩ * ⟨n, hnC⟩ * ⟨w, hwC⟩⁻¹, (inferInstance : O.Normal).conj_mem _ hnO _, rfl⟩
  have hoM : o ∈ M := by
    obtain ⟨o', ho', he⟩ := hoO
    rw [← he]
    exact hXM (mem_d1PlusCore_of_mem_core ho')
  set l := g * w * g⁻¹ * w⁻¹ with hl
  have hlL : l ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLM hgM) w).mp hwL) (L.inv_mem hwL)
  have he : g * t * g⁻¹ * t⁻¹ = l * o := by
    have ht : t = w * x := by rw [hxdef]; group
    rw [hl, ho, hn, ht]
    group
  rw [he] at hz ⊢
  obtain ⟨e, hze⟩ := hz
  have hcard : Nat.Coprime (Nat.card Ob) p := by
    rw [hOb, Subgroup.card_map_of_injective C.subtype_injective]
    exact (primeComplementCore_coprime p).symm
  obtain ⟨l', hl', hpow⟩ := exists_pow_mul_eq hlL (hLM hoM) (Nat.card Ob)
  have hoc : o ^ Nat.card Ob = 1 := by
    have := pow_card_eq_one' (G := ↥Ob) (x := ⟨o, hoO⟩)
    exact congrArg Subtype.val this
  refine mem_of_pow_mem_of_coprime' (Nat.Coprime.pow_right e hcard) ?_ ?_
  · rw [hpow, hoc, mul_one]
    exact hl'
  · rw [hze]
    exact L.one_mem

theorem inf_hyp111Pre_le (hI2 : KFactStepThreeIrred) (hSt : StepThreeGroup p ↥K)
    (hZ : Subgroup.center ↥K = ⊥) (hnp : ¬ CFSG.HasNormalPComplement p ↥K)
    {B L M : Subgroup G} (hBC : CFSG.ABGLocalTools.IsSylowOf p B C)
    (hLM : M ≤ Subgroup.normalizer (L : Set G)) (hXM : d1PlusCore p C K ≤ M)
    (hN₀M : ∀ k ∈ hyp111Pre p C K,
      k ∈ Subgroup.normalizer ((B ⊓ hyp111Pre p C K : Subgroup G) : Set G) → k ∈ M)
    (h3 : ∀ u ∈ B ⊓ hyp111Pre p C K, ∃ w ∈ C ⊓ L, w⁻¹ * u ∈ d1PlusCore p C K) :
    B ⊓ hyp111Pre p C K ≤ L := by
  set O := primeComplementCore (G := C) p with hO
  set Kp := hyp111Pre p C K with hKp
  set B₁ := B ⊓ Kp with hB₁
  set Kc : Subgroup C := K.comap (QuotientGroup.mk' O) with hKc
  have hKpC : Kp ≤ C := Subgroup.map_subtype_le _
  have hKpc : Kp.subgroupOf C = Kc :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  set θ : ↥Kc →* ↥K := (QuotientGroup.mk' O).subgroupComap K with hθ
  have hθs : Function.Surjective θ :=
    MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective O)
  set ι : ↥Kc →* G := C.subtype.comp Kc.subtype with hι
  have hker : Nat.Coprime (Nat.card θ.ker) p := by
    let f : ↥θ.ker →* ↥O :=
      { toFun := fun y => ⟨((y : ↥Kc) : C), (QuotientGroup.eq_one_iff _).mp
          (congrArg Subtype.val (MonoidHom.mem_ker.mp y.2))⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b hab => by
      have h := congrArg (fun z : ↥O => (z : C)) hab
      exact Subtype.ext (Subtype.ext h)
    exact (primeComplementCore_coprime p).symm.coprime_dvd_left
      (Subgroup.card_dvd_of_injective f hf)
  have hB₁syl : CFSG.ABGLocalTools.IsSylowOf p B₁ Kp :=
    hBC.inf_of_le_normalizer hKpC (le_normalizer_hyp111Pre hK)
  have hB₁c : CFSG.ABGLocalTools.IsSylowOf p (B₁.subgroupOf C) Kc := by
    rw [← hKpc, ← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_right.trans hKpC),
      inf_eq_left.mpr hKpC]
    exact hB₁syl
  obtain ⟨Q, hQ⟩ := hB₁c
  have hmemQ : ∀ y : ↥Kc, y ∈ (Q : Subgroup ↥Kc) ↔ ι y ∈ B₁ := by
    intro y
    constructor
    · intro hy
      have h : (y : C) ∈ (Q : Subgroup ↥Kc).map Kc.subtype := ⟨y, hy, rfl⟩
      rw [hQ] at h
      exact Subgroup.mem_subgroupOf.mp h
    · intro hy
      have h : (y : C) ∈ B₁.subgroupOf C := Subgroup.mem_subgroupOf.mpr hy
      rw [← hQ] at h
      obtain ⟨y', hy', he⟩ := h
      rwa [Subtype.ext he] at hy'
  have hιK : ∀ y : ↥Kc, ι y ∈ Kp := fun y => ⟨(y : C), y.2, rfl⟩
  have hpreK : ∀ h ∈ Kp, ∃ y : ↥Kc, ι y = h := by
    rintro _ ⟨h', hh', rfl⟩
    exact ⟨⟨h', hh'⟩, rfl⟩
  have hconj : ∀ g ∈ Subgroup.normalizer ((Q : Subgroup ↥Kc) : Set ↥Kc), ∀ h ∈ B₁,
      ι g * h * (ι g)⁻¹ ∈ B₁ := by
    intro g hg h hh
    obtain ⟨y, rfl⟩ := hpreK h hh.2
    have hyQ := (hmemQ y).mpr hh
    have := (hmemQ _).mp ((Subgroup.mem_normalizer_iff.mp hg y).mp hyQ)
    simpa using this
  have hgM : ∀ g ∈ Subgroup.normalizer ((Q : Subgroup ↥Kc) : Set ↥Kc), ι g ∈ M := by
    intro g hg
    refine hN₀M _ (hιK g) (Subgroup.mem_normalizer_iff.mpr fun h => ⟨hconj g hg h, fun hh => ?_⟩)
    have := hconj g⁻¹ (Subgroup.inv_mem _ hg) _ hh
    simpa [mul_assoc] using this
  have hcommL : ∀ g ∈ Subgroup.normalizer ((Q : Subgroup ↥Kc) : Set ↥Kc), ∀ t ∈ (Q : Subgroup ↥Kc),
      ι (g * t * g⁻¹ * t⁻¹) ∈ L := by
    intro g hg t ht
    have hzQ : g * t * g⁻¹ * t⁻¹ ∈ (Q : Subgroup ↥Kc) :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hg t).mp ht) (Subgroup.inv_mem _ ht)
    obtain ⟨e, he⟩ := Q.2 ⟨_, hzQ⟩
    obtain ⟨w, ⟨hwC, hwL⟩, hwx⟩ := h3 (ι t) ((hmemQ t).mp ht)
    have h := comm_mem_of_mem_hyp111Pre hZ hLM hXM (hιK g) (hgM g hg) hwC hwL hwx
      ⟨e, by simpa using congrArg (fun z : ↥(Q : Subgroup ↥Kc) => ι (z : ↥Kc)) he⟩
    simpa using h
  have hirr := irred_of_irred_map θ hker hθs Q (hI2 p ↥K hSt (Q.mapSurjective hθs)).1
  set V : Subgroup ↥Kc := (Q : Subgroup ↥Kc) ⊓ L.comap ι with hV
  by_cases hVΦ : V ≤ (frattini ↥(Q : Subgroup ↥Kc)).map (Q : Subgroup ↥Kc).subtype
  · exfalso
    refine hnp (hasNormalPComplement_of_surjective' θ hθs
      (hasNormalPComplement_of_comm_mem_frattini_sylow Q hirr fun g hg t ht => hVΦ ⟨?_, ?_⟩))
    · exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hg t).mp ht)
        (Subgroup.inv_mem _ ht)
    · exact hcommL g hg t ht
  · have hNV : Subgroup.normalizer ((Q : Subgroup ↥Kc) : Set ↥Kc) ≤
        Subgroup.normalizer (V : Set ↥Kc) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hg, Subgroup.le_normalizer_comap ι (hLM (hgM g hg))⟩
    have heq := hirr V inf_le_left hVΦ hNV
    intro u hu
    obtain ⟨y, rfl⟩ := hpreK u hu.2
    have hyV : y ∈ V := heq ▸ (hmemQ y).mpr hu
    exact hyV.2

end Generic

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
