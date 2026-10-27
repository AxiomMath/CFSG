module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootQc
public import CFSG.LocalAnalysis.EvenBN.TwoF4.IndexTwoTransfer

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

abbrev liftG (M : Subgroup d.Xb) : Subgroup G := (M.comap d.piA).map d.NA.subtype

theorem mem_liftG {M : Subgroup d.Xb} {x : G} :
    x ∈ d.liftG M ↔ ∃ hx : x ∈ d.NA, d.piA ⟨x, hx⟩ ∈ M := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxM⟩
    exact ⟨⟨x, hx⟩, hxM, rfl⟩

theorem liftG_le_NA (M : Subgroup d.Xb) : d.liftG M ≤ d.NA := map_subtype_le _

theorem A_le_liftG (M : Subgroup d.Xb) : d.A ≤ d.liftG M := fun a ha =>
  d.mem_liftG.2 ⟨le_normalizer ha, by
    rw [(d.piA_eq_one_iff ⟨a, le_normalizer ha⟩).2 ha]
    exact one_mem _⟩

theorem liftG_mono {M M' : Subgroup d.Xb} (hMM : M ≤ M') : d.liftG M ≤ d.liftG M' :=
  map_mono (comap_mono hMM)

theorem t_mem_normalizer_liftG {M : Subgroup d.Xb} (ht : d.tb ∈ normalizer (M : Set d.Xb)) :
    h.t ∈ normalizer (d.liftG M : Set G) := by
  have key : ∀ {s : d.NA}, d.piA s ∈ normalizer (M : Set d.Xb) → ∀ x ∈ d.liftG M,
      (s : G) * x * (s : G)⁻¹ ∈ d.liftG M := by
    intro s hs x hx
    obtain ⟨hxN, hxM⟩ := d.mem_liftG.1 hx
    refine d.mem_liftG.2 ⟨mul_mem (mul_mem s.2 hxN) (inv_mem s.2), ?_⟩
    have : d.piA (s * ⟨x, hxN⟩ * s⁻¹) ∈ M := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 hs _).1 hxM
    exact this
  refine mem_normalizer_of_conj_mem (key (s := d.tN) ht) fun x hx => ?_
  have := key (s := d.tN⁻¹) (by rw [map_inv]; exact inv_mem ht) x hx
  simpa using this

theorem mem_liftG_iff_of_mem {M : Subgroup d.Xb} (x : d.NA) :
    (x : G) ∈ d.liftG M ↔ d.piA x ∈ M := by
  rw [d.mem_liftG]
  exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨x.2, hx⟩⟩

theorem freeSeries_Q {W : Subgroup d.Xb} (hB : BenderSylow W d.tb (d.bar (h.V .i1)) W) :
    FreeSeries h.t ![⊥, d.A1, d.A1 ⊔ d.W, d.A, d.liftG (zIn W), d.liftG W] := by
  have hA := d.freeSeries_A
  have hW := hB.freeSeries
  have htt : d.tb * d.tb = 1 := hB.mul_self
  have hlift : ∀ {M M' : Subgroup d.Xb},
      (∀ x ∈ M', d.tb⁻¹ * x⁻¹ * d.tb * x ∈ M → ∃ y ∈ M', x⁻¹ * (y⁻¹ * (d.tb⁻¹ * y * d.tb)) ∈ M) →
      ∀ x ∈ d.liftG M', h.t⁻¹ * x⁻¹ * h.t * x ∈ d.liftG M →
        ∃ y ∈ d.liftG M', x⁻¹ * (y⁻¹ * (h.t⁻¹ * y * h.t)) ∈ d.liftG M := by
    intro M M' hMM x hx hxt
    obtain ⟨hxN, hxM'⟩ := d.mem_liftG.1 hx
    set xN : d.NA := ⟨x, hxN⟩
    have hxt' : d.tb⁻¹ * (d.piA xN)⁻¹ * d.tb * d.piA xN ∈ M := by
      have := (d.mem_liftG_iff_of_mem (d.tN⁻¹ * xN⁻¹ * d.tN * xN)).1 hxt
      simpa using this
    obtain ⟨yb, hyb, hy⟩ := hMM _ hxM' hxt'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective d.AN yb
    refine ⟨y, (d.mem_liftG_iff_of_mem y).2 hyb, ?_⟩
    have := (d.mem_liftG_iff_of_mem (xN⁻¹ * (y⁻¹ * (d.tN⁻¹ * y * d.tN)))).2 (by simpa using hy)
    simpa using this
  have hZW : zIn W ≤ W := zIn_le W
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact bot_le
    · exact le_sup_left
    · exact d.A1_sup_W_le_A
    · exact d.A_le_liftG _
    · exact d.liftG_mono hZW
  · intro i
    fin_cases i
    · exact hA.le_normalizer 0
    · exact hA.le_normalizer 1
    · exact hA.le_normalizer 2
    · exact d.liftG_le_NA _
    · change d.liftG W ≤ normalizer (d.liftG (zIn W) : Set G)
      have hn : W ≤ normalizer (zIn W : Set d.Xb) := le_normalizer_zIn W
      have key : ∀ {s : d.NA}, d.piA s ∈ W → ∀ x ∈ d.liftG (zIn W),
          (s : G) * x * (s : G)⁻¹ ∈ d.liftG (zIn W) := by
        intro s hs x hx
        obtain ⟨hxN, hxM⟩ := d.mem_liftG.1 hx
        refine d.mem_liftG.2 ⟨mul_mem (mul_mem s.2 hxN) (inv_mem s.2), ?_⟩
        have : d.piA (s * ⟨x, hxN⟩ * s⁻¹) ∈ zIn W := by
          rw [map_mul, map_mul, map_inv]
          exact (mem_normalizer_iff.1 (hn hs) _).1 hxM
        exact this
      intro q hq
      obtain ⟨hqN, hqW⟩ := d.mem_liftG.1 hq
      refine mem_normalizer_of_conj_mem (key (s := ⟨q, hqN⟩) hqW) fun x hx => ?_
      have := key (s := (⟨q, hqN⟩ : d.NA)⁻¹) (by rw [map_inv]; exact inv_mem hqW) x hx
      simpa using this
  · intro i
    fin_cases i
    · exact hA.mem_normalizer 0
    · exact hA.mem_normalizer 1
    · exact hA.mem_normalizer 2
    · exact hA.mem_normalizer 3
    · exact d.t_mem_normalizer_liftG (mem_normalizer_zIn hB.mem_normalizer)
    · exact d.t_mem_normalizer_liftG hB.mem_normalizer
  · intro i
    fin_cases i
    · exact hA.mul_self_mem 0
    · exact hA.mul_self_mem 1
    · exact hA.mul_self_mem 2
    · intro x hx
      change x * x ∈ d.A
      obtain ⟨hxN, hxM⟩ := d.mem_liftG.1 hx
      have h1 : d.piA (⟨x, hxN⟩ * ⟨x, hxN⟩) = 1 := by
        rw [map_mul]
        exact hB.center_mul_self _ hxM
      exact (d.piA_eq_one_iff _).1 h1
    · intro x hx
      change x * x ∈ d.liftG (zIn W)
      obtain ⟨hxN, hxM⟩ := d.mem_liftG.1 hx
      refine d.mem_liftG.2 ⟨mul_mem hxN hxN, ?_⟩
      have : d.piA (⟨x, hxN⟩ * ⟨x, hxN⟩) ∈ zIn W := by
        rw [map_mul]
        exact hB.mul_self_mem _ hxM
      exact this
  · intro i
    fin_cases i
    · exact hA.exists_commutator 0
    · exact hA.exists_commutator 1
    · exact hA.exists_commutator 2
    · intro x hx hxt
      change x ∈ d.liftG (zIn W) at hx
      change h.t⁻¹ * x⁻¹ * h.t * x ∈ d.A at hxt
      change ∃ y ∈ d.liftG (zIn W), x⁻¹ * (y⁻¹ * (h.t⁻¹ * y * h.t)) ∈ d.A
      have hbot : ∀ x ∈ zIn W, d.tb⁻¹ * x⁻¹ * d.tb * x ∈ (⊥ : Subgroup d.Xb) →
          ∃ y ∈ zIn W, x⁻¹ * (y⁻¹ * (d.tb⁻¹ * y * d.tb)) ∈ (⊥ : Subgroup d.Xb) :=
        hW.exists_commutator 0
      have hAbot : d.liftG ⊥ = d.A := by
        refine le_antisymm (fun y hy => ?_) (d.A_le_liftG _)
        obtain ⟨hyN, hyM⟩ := d.mem_liftG.1 hy
        rw [mem_bot] at hyM
        exact (d.piA_eq_one_iff _).1 hyM
      rw [← hAbot] at hxt ⊢
      exact hlift hbot x hx hxt
    · intro x hx hxt
      change x ∈ d.liftG W at hx
      change h.t⁻¹ * x⁻¹ * h.t * x ∈ d.liftG (zIn W) at hxt
      change ∃ y ∈ d.liftG W, x⁻¹ * (y⁻¹ * (h.t⁻¹ * y * h.t)) ∈ d.liftG (zIn W)
      exact hlift (hW.exists_commutator 1) x hx hxt

include d in
theorem false_of_gms (hGMS : GMSK.GMSSuzukiSharpKRankOneStatement)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  obtain ⟨W, hB⟩ := d.exists_benderSylow_Xb hGMS hK
  set Q := d.liftG W with hQ
  have hFS := d.freeSeries_Q hB
  have h13 := (miyamoto_lemma_1_3 h.ht hFS).1
  have htQ : h.t ∈ normalizer (Q : Set G) := d.t_mem_normalizer_liftG hB.mem_normalizer
  have htnQ : h.t ∉ Q := fun ht => hB.not_mem_W ((d.mem_liftG_iff_of_mem d.tN).1 ht)
  have hidx : Q.relIndex (Q ⊔ zpowers h.t) = 2 := by
    have hcard := card_sup_mul_card_inf_of_le_normalizer' (zpowers_le.2 htQ)
    have hinf : Q ⊓ zpowers h.t = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases eq_one_or_eq_of_mem_zpowers h.t_mul_t (mem_inf.1 hx).2 with h1 | h1
      · rw [h1]; exact one_mem _
      · exact absurd (h1 ▸ (mem_inf.1 hx).1) htnQ
    rw [hinf, Subgroup.card_bot, mul_one, h.card_zpowers_t] at hcard
    have h2 := Subgroup.relIndex_mul_card (H := Q) (K := Q ⊔ zpowers h.t)
    rw [inf_of_le_left le_sup_left] at h2
    rw [hcard] at h2
    have hpos : 0 < Nat.card Q := Nat.card_pos
    nlinarith
  have hfus : ∀ g : G, g⁻¹ * h.t * g ∈ Q ⊔ zpowers h.t → g⁻¹ * h.t * g ∉ Q →
      ∃ x ∈ Q ⊔ zpowers h.t, g⁻¹ * h.t * g = x⁻¹ * h.t * x := by
    intro g hg hgQ
    obtain ⟨q, hq, hc | hc⟩ := h.exists_eq_or_eq_mul_t htQ hg
    · exact absurd (hc ▸ hq) hgQ
    · have hmem : g⁻¹ * h.t * g ∈
          {x | (∃ y ∈ Q, x = h.t * y) ∧ orderOf x = 2} := by
        refine ⟨⟨h.t⁻¹ * q * h.t, ?_, ?_⟩, ?_⟩
        · have := (mem_normalizer_iff.1 (inv_mem htQ) q).1 hq
          rwa [inv_inv] at this
        · rw [hc]; group
        · rw [show g⁻¹ * h.t * g = MulAut.conj g⁻¹ h.t by simp, MulEquiv.orderOf_eq, h.ht]
      have hmem' : g⁻¹ * h.t * g ∈ {x | (∃ y ∈ (![⊥, d.A1, d.A1 ⊔ d.W, d.A, d.liftG (zIn W),
          d.liftG W] : Fin 6 → Subgroup G) (Fin.last 5), x = h.t * y) ∧ orderOf x = 2} := hmem
      rw [h13] at hmem'
      obtain ⟨y, hy, hgy⟩ := hmem'
      exact ⟨y, mem_sup_left hy, hgy⟩
  have hV1Q : h.V .i1 ≤ Q := fun v hv => by
    have hvN : v ∈ d.NA := ((h.V_le_N .i1).trans d.N1_le_NA) hv
    exact (d.mem_liftG_iff_of_mem ⟨v, hvN⟩).2 (hB.le ⟨⟨v, hvN⟩, mem_subgroupOf.2 hv, rfl⟩)
  have hPQ : h.P ≤ Q :=
    h.P_le_R_sup_V1.trans (sup_le (d.R_le_A.trans (d.A_le_liftG _)) hV1Q)
  have hsyl : ¬ 2 ∣ (Q ⊔ zpowers h.t).relIndex (centralizer ({h.t} : Set G)) := by
    have hPT := h.isSylowOf_P_sup_Tsyl
    rw [h.sec3_1.1] at hPT
    have hle1 : h.P ⊔ zpowers h.t ≤ (Q ⊔ zpowers h.t) ⊓ h.C :=
      le_inf (sup_le_sup_right hPQ _) hPT.le
    obtain ⟨-, -, hodd⟩ := isSylowOf_iff.1 hPT
    have e := Subgroup.relIndex_mul_relIndex (h.P ⊔ zpowers h.t) ((Q ⊔ zpowers h.t) ⊓ h.C) h.C
      hle1 inf_le_right
    rw [Subgroup.inf_relIndex_right] at e
    intro h2
    exact hodd (e ▸ dvd_mul_of_dvd_right h2 _)
  exact false_of_index_two_coset_conj h.nonab h.ht hidx (mem_sup_right (mem_zpowers _)) htnQ
    hfus hsyl

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
