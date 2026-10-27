module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transfer
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open scoped Pointwise

variable {X : Type} [Group X]

theorem Frame.exists_sylowFrame [Finite X] {G T : Subgroup X} (hF : Frame G T) :
    ∃ S : Subgroup X, SylowFrame G T S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (G ⊔ T) ⊓ Subgroup.normalizer (T : Set X)
  have hTN : T ≤ N := le_inf le_sup_right Subgroup.le_normalizer
  obtain ⟨P, hP, hTP⟩ := exists_isSylowOf_le hF.isPGroup hTN
  obtain ⟨S, hS, hPS⟩ := exists_isSylowOf_le hP.isPGroup (hP.le.trans inf_le_left)
  refine ⟨S, { toFrame := hF, sylow := hS, sylow_normalizer := ?_ }⟩
  have heq := hP.eq_of_le (le_inf hPS (hP.le.trans inf_le_right))
    (inf_le_inf_right _ hS.le) hS.isPGroup.to_inf_left
  rw [heq]
  exact hP

theorem IsSylowOf.map [Finite X] {Y : Type*} [Group Y] {p : ℕ} [Fact p.Prime] {P K : Subgroup X}
    (h : IsSylowOf p P K) (f : X →* Y) : IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

namespace Frame

variable {G T : Subgroup X}

theorem map (hF : Frame G T) (N : Subgroup X) [N.Normal] (hN : N ≤ G) :
    Frame (G.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N)) where
  le_normalizer := (Subgroup.map_mono hF.le_normalizer).trans (Subgroup.le_normalizer_map _)
  inf_eq_bot := by
    rw [eq_bot_iff]
    rintro x ⟨⟨t, ht, rfl⟩, ⟨g, hg, hgt⟩⟩
    have hmem : g⁻¹ * t ∈ N := QuotientGroup.eq.mp hgt
    have htG : t ∈ G := by simpa using G.mul_mem hg (hN hmem)
    have ht1 : t ∈ T ⊓ G := ⟨ht, htG⟩
    rw [hF.inf_eq_bot, Subgroup.mem_bot] at ht1
    rw [Subgroup.mem_bot, ht1, map_one]
  isPGroup := hF.isPGroup.map _

end Frame

theorem isSylowOf_sup_odd [Finite X] {T N : Subgroup X} [N.Normal] (hT : IsPGroup 2 T)
    (hodd : Odd (Nat.card N)) (hTN : T ⊓ N = ⊥) : IsSylowOf 2 T (T ⊔ N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨le_sup_left, hT, ?_⟩
  have hNT : T ≤ Subgroup.normalizer (N : Set X) := fun t _ =>
    Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => (inferInstance : N.Normal).conj_mem n hn t,
      fun hn => by simpa [mul_assoc] using (inferInstance : N.Normal).conj_mem _ hn t⁻¹⟩
  have hcard : Nat.card (T ⊔ N : Subgroup X) = Nat.card T * Nat.card N := by
    rw [sup_comm, card_sup_of_le_normalizer hNT (by rw [inf_comm]; exact hTN), mul_comm]
  have hrel := Subgroup.relIndex_mul_card T (T ⊔ N)
  rw [inf_eq_left.mpr le_sup_left, hcard] at hrel
  have hrelN : T.relIndex (T ⊔ N) = Nat.card N := by
    have hpos : 0 < Nat.card T := Nat.card_pos
    rw [mul_comm (Nat.card T)] at hrel
    exact Nat.eq_of_mul_eq_mul_right hpos hrel
  rw [hrelN]
  exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

namespace SylowFrame

variable {G T S : Subgroup X}

theorem map_normalizer_odd [Finite X] (hF : Frame G T) (N : Subgroup X) [N.Normal] (hN : N ≤ G)
    (hodd : Odd (Nat.card N)) :
    Subgroup.normalizer ((T.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) =
      (Subgroup.normalizer (T : Set X)).map (QuotientGroup.mk' N) := by
  set π := QuotientGroup.mk' N
  have hTN : T ⊓ N = ⊥ := by
    rw [eq_bot_iff, ← hF.inf_eq_bot]
    exact inf_le_inf_left T hN
  have hsyl := isSylowOf_sup_odd hF.isPGroup hodd hTN
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    have hle : rightConjugate T x⁻¹ ≤ T ⊔ N := by
      intro w hw
      rw [mem_rightConjugate_iff, inv_inv] at hw
      have hw' : x⁻¹ * w * x⁻¹⁻¹ ∈ T := by simpa using hw
      have hπ : π w ∈ T.map π := by
        have h1 := (Subgroup.mem_normalizer_iff.mp hz (π (x⁻¹ * w * x⁻¹⁻¹))).mp
          (Subgroup.mem_map_of_mem π hw')
        simpa [π, mul_assoc] using h1
      obtain ⟨t, ht, hte⟩ := hπ
      have hmem : t⁻¹ * w ∈ N := QuotientGroup.eq.mp hte
      have := Subgroup.mul_mem _ (Subgroup.mem_sup_left ht : t ∈ T ⊔ N)
        (Subgroup.mem_sup_right hmem : t⁻¹ * w ∈ T ⊔ N)
      simpa using this
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsyl' : IsSylowOf 2 (rightConjugate T x⁻¹) (T ⊔ N) :=
      isSylowOf_of_card hle (by rw [rightConjugate_card, hsyl.card_eq])
    obtain ⟨c, hc, hceq⟩ := exists_rightConjugate_eq_of_isSylowOf hsyl' hsyl
    have hcx : c * x ∈ Subgroup.normalizer (T : Set X) := by
      rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hceq, rightConjugate_mul,
        inv_mul_cancel, rightConjugate_one]
    have hc' : c⁻¹ ∈ (T : Set X) * (N : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T N (by
        intro y _
        exact Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn =>
          (inferInstance : N.Normal).conj_mem n hn y,
          fun hn => by simpa [mul_assoc] using (inferInstance : N.Normal).conj_mem _ hn y⁻¹⟩)]
      exact (T ⊔ N).inv_mem hc
    obtain ⟨t, ht, n, hn, htn⟩ := Set.mem_mul.mp hc'
    refine ⟨t * (c * x), Subgroup.mul_mem _ (Subgroup.le_normalizer ht) hcx, ?_⟩
    have hx : x = t * n * (c * x) := by rw [htn]; group
    have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    calc π (t * (c * x)) = π t * π (c * x) := map_mul _ _ _
      _ = π t * π n * π (c * x) := by rw [hπn, mul_one]
      _ = π (t * n * (c * x)) := by simp only [map_mul]
      _ = π x := by rw [← hx]
  · exact Subgroup.le_normalizer_map _

theorem map_odd [Finite X] (h : SylowFrame G T S) (htop : G ⊔ T = ⊤) (N : Subgroup X)
    [N.Normal] (hN : N ≤ G) (hodd : Odd (Nat.card N)) :
    SylowFrame (G.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N))
      (S.map (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N
  have hsup : G.map π ⊔ T.map π = ⊤ := by
    rw [← Subgroup.map_sup, htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  refine { toFrame := h.toFrame.map N hN, sylow := ?_, sylow_normalizer := ?_ }
  · rw [← Subgroup.map_sup]
    exact IsSylowOf.map h.sylow π
  · rw [hsup, top_inf_eq, map_normalizer_odd h.toFrame N hN hodd]
    have hsyl := IsSylowOf.map h.sylow_normalizer π
    rw [htop, top_inf_eq] at hsyl
    have heq := hsyl.eq_of_le (le_inf (Subgroup.map_mono inf_le_left)
      (Subgroup.map_mono inf_le_right)) inf_le_right ((h.sylow.isPGroup.map π).to_inf_left)
    rw [heq]
    exact hsyl

end SylowFrame

namespace Hyp43

variable {G T Q H : Subgroup X}

theorem map_odd [Finite X] (hF : Frame G T) (h : Hyp43 G T Q H) (htop : G ⊔ T = ⊤)
    (N : Subgroup X) [N.Normal] (hN : N ≤ G) (hodd : Odd (Nat.card N)) :
    Hyp43 (G.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N))
      (Q.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N)) where
  le := Subgroup.map_mono h.le
  le_normalizer := (Subgroup.map_mono h.le_normalizer).trans (Subgroup.le_normalizer_map _)
  le_sup := by
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono h.le_sup
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsSylowOf.map h.sylow _
  inf_eq_bot := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set π := QuotientGroup.mk' N
    rintro _ ⟨g, hg, rfl⟩ hgH
    by_contra hne
    obtain ⟨⟨x, hxT, hxg⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨t, ht, rfl⟩ := hxT
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hx1 (Subtype.ext (map_one π))
    have hxg' := (mem_rightConjugate_iff _ _ _).mp hxg
    rw [← map_inv, ← map_mul, ← map_mul] at hxg'
    obtain ⟨t', ht', hte⟩ := hxg'
    have hmem : t'⁻¹ * (g * t * g⁻¹) ∈ N := QuotientGroup.eq.mp hte
    have hTN : T ⊓ N = ⊥ := by
      rw [eq_bot_iff, ← hF.inf_eq_bot]
      exact inf_le_inf_left T hN
    have hsyl := isSylowOf_sup_odd hF.isPGroup hodd hTN
    have hgt : g * t * g⁻¹ ∈ T ⊔ N := by
      have := Subgroup.mul_mem _ (Subgroup.mem_sup_left ht' : t' ∈ T ⊔ N)
        (Subgroup.mem_sup_right hmem : t'⁻¹ * (g * t * g⁻¹) ∈ T ⊔ N)
      simpa using this
    have hZ : IsPGroup 2 (Subgroup.zpowers (g * t * g⁻¹)) := by
      have hle : Subgroup.zpowers t ≤ T := (Subgroup.zpowers_le).mpr ht
      have hconj : (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom =
          Subgroup.zpowers (g * t * g⁻¹) := by
        rw [MonoidHom.map_zpowers]
        rfl
      rw [← hconj]
      exact (hF.isPGroup.to_le hle).map _
    obtain ⟨y, hy, hyle⟩ := exists_rightConjugate_le_of_isSylowOf hsyl hZ
      ((Subgroup.zpowers_le).mpr hgt)
    have hyt : y⁻¹ * (g * t * g⁻¹) * y ∈ T :=
      hyle (conj_mem_rightConjugate (Subgroup.mem_zpowers _) y)
    have htc : t ∈ T ⊓ rightConjugate T (y⁻¹ * g) := by
      refine ⟨ht, (mem_rightConjugate_iff _ _ _).mpr ?_⟩
      simpa [mul_assoc] using hyt
    have hcH : y⁻¹ * g ∈ H := by
      apply h.mem_of_inf_ne_bot_sup hF (by rw [htop]; exact Subgroup.mem_top _)
      intro hbot
      rw [hbot, Subgroup.mem_bot] at htc
      exact ht1 htc
    apply hgH
    have hyT : π y ∈ T.map π := by
      have hy' : y ∈ (T : Set X) * (N : Set X) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right T N (fun z _ =>
          Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn =>
            (inferInstance : N.Normal).conj_mem n hn z,
            fun hn => by simpa [mul_assoc] using (inferInstance : N.Normal).conj_mem _ hn z⁻¹⟩)]
        exact hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hy'
      refine ⟨a, ha, ?_⟩
      have hπb : π b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
      rw [map_mul, hπb, mul_one]
    have hg' : g = y * (y⁻¹ * g) := by group
    rw [hg', map_mul]
    exact Subgroup.mul_mem _ (Subgroup.map_mono h.le_H hyT) (Subgroup.mem_map_of_mem π hcH)

end Hyp43

theorem isSylowOf_sup_of_isSylowOf [Finite X] {P K₀ T : Subgroup X} (hP : IsSylowOf 2 P K₀)
    (hT : IsPGroup 2 T) (hTK : T ≤ Subgroup.normalizer (K₀ : Set X))
    (hTP : T ≤ Subgroup.normalizer (P : Set X)) (hinf : K₀ ⊓ T = ⊥) :
    IsSylowOf 2 (P ⊔ T) (K₀ ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨hPK, hP2, hdvd⟩ := hP
  refine ⟨sup_le_sup_right hPK T, IsPGroup.to_sup_of_normal_left' hP2 hT hTP, ?_⟩
  have hPT : P ⊓ T = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf_right T hPK
  have hcP : Nat.card (P ⊔ T : Subgroup X) = Nat.card P * Nat.card T :=
    card_sup_of_le_normalizer hTP hPT
  have hcK : Nat.card (K₀ ⊔ T : Subgroup X) = Nat.card K₀ * Nat.card T :=
    card_sup_of_le_normalizer hTK hinf
  have h1 := Subgroup.relIndex_mul_card (P ⊔ T) (K₀ ⊔ T)
  rw [inf_eq_left.mpr (sup_le_sup_right hPK T), hcP, hcK] at h1
  have h2 := Subgroup.relIndex_mul_card P K₀
  rw [inf_eq_left.mpr hPK] at h2
  have heq : (P ⊔ T).relIndex (K₀ ⊔ T) = P.relIndex K₀ := by
    have hpos : 0 < Nat.card P * Nat.card T := Nat.mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← mul_assoc, h2]
  rwa [heq]

namespace SylowFrame

variable {G T S : Subgroup X}

theorem restrict [Finite X] (h : SylowFrame G T S) {G₁ : Subgroup X} (hG₁ : G₁ ≤ G)
    (hn : G ⊔ T ≤ Subgroup.normalizer (G₁ : Set X)) :
    SylowFrame G₁ T (S ⊓ (G₁ ⊔ T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := h.toFrame
  have hTN : T ≤ Subgroup.normalizer (G₁ : Set X) := le_sup_right.trans hn
  have hinf : G₁ ⊓ T = ⊥ := by
    rw [eq_bot_iff, ← hF.inf_eq_bot, inf_comm]
    exact inf_le_inf_left T hG₁
  have hF₁ : Frame G₁ T := ⟨hTN, by rw [inf_comm]; exact hinf, hF.isPGroup⟩
  have hTS := h.le
  have hG₁L : G₁ ≤ G ⊔ T := hG₁.trans le_sup_left
  refine { toFrame := hF₁, sylow := ?_, sylow_normalizer := ?_ }
  · have hsyl₁ := h.sylow.inf_of_le_normalizer hG₁L hn
    have hTP : T ≤ Subgroup.normalizer ((S ⊓ G₁ : Subgroup X) : Set X) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hTS ht), hTN ht⟩
    have hsyl := isSylowOf_sup_of_isSylowOf hsyl₁ hF.isPGroup hTN hTP hinf
    have heq := hsyl.eq_of_le (le_inf (sup_le inf_le_left hTS)
      (sup_le_sup_right inf_le_right T)) inf_le_right h.sylow.isPGroup.to_inf_left
    rw [heq]
    exact hsyl
  · set NT := Subgroup.normalizer (T : Set X)
    have hsyl₁ : IsSylowOf 2 ((S ⊓ NT) ⊓ (G₁ ⊓ NT)) (G₁ ⊓ NT) :=
      h.sylow_normalizer.inf_of_le_normalizer (inf_le_inf_right NT hG₁L)
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hn hx.1, Subgroup.le_normalizer hx.2⟩)
    have hTG₁N : T ≤ Subgroup.normalizer ((G₁ ⊓ NT : Subgroup X) : Set X) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hTN ht, Subgroup.le_normalizer
        (Subgroup.le_normalizer ht)⟩
    have hTP : T ≤ Subgroup.normalizer (((S ⊓ NT) ⊓ (G₁ ⊓ NT) : Subgroup X) : Set X) :=
      fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer ⟨hTS ht, Subgroup.le_normalizer ht⟩, hTG₁N ht⟩
    have hinf' : (G₁ ⊓ NT) ⊓ T = ⊥ := by
      rw [eq_bot_iff, ← hinf]
      exact inf_le_inf_right T inf_le_left
    have hsyl := isSylowOf_sup_of_isSylowOf hsyl₁ hF.isPGroup hTG₁N hTP hinf'
    have hded : (G₁ ⊔ T) ⊓ NT = (G₁ ⊓ NT) ⊔ T := by
      apply le_antisymm
      · rintro x ⟨hx, hxN⟩
        have hx' : x ∈ (G₁ : Set X) * (T : Set X) := by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left G₁ T hTN]
          exact hx
        obtain ⟨g, hg, t, ht, rfl⟩ := Set.mem_mul.mp hx'
        have hgN : g ∈ NT := by
          simpa using NT.mul_mem hxN (NT.inv_mem (Subgroup.le_normalizer ht))
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hg, hgN⟩) (Subgroup.mem_sup_right ht)
      · exact sup_le (inf_le_inf_right NT le_sup_left) (le_inf le_sup_right Subgroup.le_normalizer)
    rw [hded]
    have hle : ((S ⊓ NT) ⊓ (G₁ ⊓ NT)) ⊔ T ≤ (S ⊓ (G₁ ⊔ T)) ⊓ NT :=
      sup_le (le_inf (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans (inf_le_left.trans le_sup_left))) (inf_le_left.trans inf_le_right))
        (le_inf (le_inf hTS le_sup_right) Subgroup.le_normalizer)
    have heq := hsyl.eq_of_le hle (by rw [← hded]; exact inf_le_inf_right NT inf_le_right)
      (h.sylow.isPGroup.to_inf_left.to_inf_left)
    rw [heq]
    exact hsyl

end SylowFrame

namespace Hyp43

variable {G T Q H : Subgroup X}

theorem restrict [Finite X] (h : Hyp43 G T Q H) {G₁ : Subgroup X} (hG₁ : G₁ ≤ G) :
    Hyp43 G₁ T (Q ⊓ (G₁ ⊔ T)) (H ⊓ (G₁ ⊔ T)) where
  le := inf_le_inf_right _ h.le
  le_normalizer := fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨h.le_normalizer hx.1, Subgroup.le_normalizer hx.2⟩
  le_sup := inf_le_right
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact h.sylow.of_le (le_inf h.le_Q le_sup_right) inf_le_left
  inf_eq_bot := fun g hg hgH => h.inf_eq_bot g (hG₁ hg) fun hgH' =>
    hgH ⟨hgH', Subgroup.mem_sup_left hg⟩

end Hyp43

theorem pRank_map_eq [Finite X] {Y : Type*} [Group Y] [Finite Y] (f : X →* Y)
    (hf : Function.Injective f) (K : Subgroup X) :
    CFSG.Open.pRank 2 (K.map f) = CFSG.Open.pRank 2 K := by
  apply le_antisymm _ (CFSG.SectionRank.pRank_le_map one_lt_two f hf K)
  obtain ⟨E, hEK, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two (K.map f)
  have hEf : E ≤ f.range := hEK.trans (Subgroup.map_le_range f K)
  have hmap : (E.comap f).map f = E := Subgroup.map_comap_eq_self hEf
  refine CFSG.SectionRank.le_pRank one_lt_two (E := E.comap f) ?_ ?_ ?_
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hEK hx
    rwa [hf hyx] at hy
  · have h1 := CFSG.SectionRank.isElemAbelian_map (p := 2) hE (MonoidHom.id Y)
    refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
    · have := hE.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩
      simpa using congrArg Subtype.val this
    · rw [map_pow, hE.2 _ hx, map_one]
  · rw [← hcard]
    calc Nat.card (E.comap f) = Nat.card ((E.comap f).map f) :=
          (Subgroup.card_map_of_injective hf).symm
      _ = Nat.card E := by rw [hmap]

theorem Frame.subgroupOf {G T : Subgroup X} (hF : Frame G T) :
    Frame (G.subgroupOf (G ⊔ T)) (T.subgroupOf (G ⊔ T)) where
  le_normalizer := by
    rw [← Subgroup.subgroupOf_normalizer_eq le_sup_left]
    exact fun x hx => hF.le_normalizer hx
  inf_eq_bot := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxG⟩
    have hmem : (x : X) ∈ T ⊓ G := ⟨hxT, hxG⟩
    rw [hF.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  isPGroup := hF.isPGroup.comap_subtype

omit [Group X] in
theorem sup_subgroupOf_eq_top {X : Type} [Group X] (G T : Subgroup X) :
    G.subgroupOf (G ⊔ T) ⊔ T.subgroupOf (G ⊔ T) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]

theorem map_subtype_inf_subgroupOf {L A B : Subgroup X} (hA : A ≤ L) :
    (A.subgroupOf L ⊓ B.subgroupOf L).map L.subtype = A ⊓ B := by
  rw [Subgroup.map_inf_eq _ _ _ L.subtype_injective, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA]
  apply le_antisymm (inf_le_inf_left A inf_le_left)
  exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hA))

theorem map_subtype_top (L : Subgroup X) : (⊤ : Subgroup L).map L.subtype = L := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem SylowFrame.subgroupOf [Finite X] {G T S : Subgroup X} (h : SylowFrame G T S) :
    SylowFrame (G.subgroupOf (G ⊔ T)) (T.subgroupOf (G ⊔ T)) (S.subgroupOf (G ⊔ T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := G ⊔ T with hLdef
  have hTL : T ≤ L := le_sup_right
  have hSL : S ≤ L := h.sylow.le
  refine { toFrame := h.toFrame.subgroupOf, sylow := ?_, sylow_normalizer := ?_ }
  · rw [sup_subgroupOf_eq_top, ← isSylowOf_map_subtype_iff L, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hSL, map_subtype_top]
    exact h.sylow
  · rw [sup_subgroupOf_eq_top, top_inf_eq, ← Subgroup.subgroupOf_normalizer_eq hTL,
      ← isSylowOf_map_subtype_iff L, map_subtype_inf_subgroupOf hSL,
      Subgroup.subgroupOf_map_subtype, inf_comm (Subgroup.normalizer (T : Set X)) L]
    exact h.sylow_normalizer

theorem Hyp43.subgroupOf [Finite X] {G T Q H : Subgroup X} (h : Hyp43 G T Q H) :
    Hyp43 (G.subgroupOf (G ⊔ T)) (T.subgroupOf (G ⊔ T)) (Q.subgroupOf (G ⊔ T))
      (H.subgroupOf (G ⊔ T)) where
  le := fun x hx => h.le hx
  le_normalizer := by
    have hQL : Q ≤ G ⊔ T := h.le.trans h.le_sup
    rw [← Subgroup.subgroupOf_normalizer_eq hQL]
    exact fun x hx => h.le_normalizer hx
  le_sup := by rw [sup_subgroupOf_eq_top]; exact le_top
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQL : Q ≤ G ⊔ T := h.le.trans h.le_sup
    rw [← isSylowOf_map_subtype_iff (G ⊔ T), Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (le_sup_right : T ≤ G ⊔ T),
      inf_eq_left.mpr hQL]
    exact h.sylow
  inf_eq_bot := by
    set L := G ⊔ T
    rintro g hg hgH
    have hbot := h.inf_eq_bot g hg hgH
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_bot, Subgroup.map_inf_eq _ _ _ L.subtype_injective, map_rightConjugate,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (le_sup_right : T ≤ L)]
    exact hbot

end CFSG.ComponentClassification.AschbacherTheorem3
