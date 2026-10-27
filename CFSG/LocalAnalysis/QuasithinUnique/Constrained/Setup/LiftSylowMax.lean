module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDirect
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin.B6 CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.Layer

variable {H : Type*} [Group H]

@[expose] def localNormalizer (T L : Subgroup H) : Subgroup H :=
  Subgroup.normalizer ((T ⊓ L : Subgroup H) : Set H) ⊓ L

theorem inf_le_localNormalizer (T L : Subgroup H) : T ⊓ L ≤ localNormalizer T L :=
  le_inf Subgroup.le_normalizer inf_le_right

theorem localNormalizer_le (T L : Subgroup H) : localNormalizer T L ≤ L := inf_le_right

theorem mem_normalizer_inf {A B : Subgroup H} {g : H} (hA : g ∈ Subgroup.normalizer (A : Set H))
    (hB : g ∈ Subgroup.normalizer (B : Set H)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup H) : Set H) :=
  Subgroup.mem_normalizer_iff.2 fun h =>
    and_congr (Subgroup.mem_normalizer_iff.1 hA h) (Subgroup.mem_normalizer_iff.1 hB h)

theorem mem_normalizer_iSup {ι : Sort*} (Y : ι → Subgroup H) {g : H}
    (h : ∀ j, g ∈ Subgroup.normalizer (Y j : Set H)) :
    g ∈ Subgroup.normalizer ((⨆ j, Y j : Subgroup H) : Set H) := by
  refine mem_normalizer_of_conjSub_le ?_ ?_
  · rw [show conjSub g (⨆ j, Y j) = ⨆ j, conjSub g (Y j) from OrderIso.map_iSup _ _]
    exact iSup_mono fun j => le_of_eq (conjSub_eq_self (h j))
  · rw [show conjSub g⁻¹ (⨆ j, Y j) = ⨆ j, conjSub g⁻¹ (Y j) from OrderIso.map_iSup _ _]
    exact iSup_mono fun j => le_of_eq (conjSub_eq_self (Subgroup.inv_mem _ (h j)))

theorem conj_normalizes_of_normal_sylow [Finite H] {p : ℕ} [Fact p.Prime] {B U : Subgroup H}
    (Q : Sylow p ↥B) (hQ : (Q : Subgroup ↥B) = U.subgroupOf B) (hUB : U ≤ B)
    (hn : (U.subgroupOf B).Normal) {g : H} (hg : g ∈ Subgroup.normalizer (B : Set H)) :
    g ∈ Subgroup.normalizer (U : Set H) := by
  have hQn : (Q : Subgroup ↥B).Normal := by rw [hQ]; exact hn
  have hchar := Sylow.characteristic_of_normal Q hQn
  have key : ∀ g' ∈ Subgroup.normalizer (B : Set H), ∀ u ∈ U, g' * u * g'⁻¹ ∈ U := by
    intro g' hg' u hu
    let φ' : MulAut ↥B := B.normalizerMonoidHom ⟨g', hg'⟩
    have h1 : (Q : Subgroup ↥B).map φ'.toMonoidHom = (Q : Subgroup ↥B) :=
      Subgroup.characteristic_iff_map_eq.1 hchar φ'
    have hu' : (⟨u, hUB hu⟩ : ↥B) ∈ (Q : Subgroup ↥B) := by rw [hQ]; exact hu
    have h2 : φ' ⟨u, hUB hu⟩ ∈ (Q : Subgroup ↥B) := by rw [← h1]; exact ⟨_, hu', rfl⟩
    rw [hQ] at h2
    have e : ((φ' ⟨u, hUB hu⟩ : ↥B) : H) = g' * u * g'⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe B ⟨g', hg'⟩ ⟨u, hUB hu⟩
    have h3 : ((φ' ⟨u, hUB hu⟩ : ↥B) : H) ∈ U := h2
    rwa [e] at h3
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key g hg x hx
  · intro hx
    have := key g⁻¹ ((Subgroup.normalizer (B : Set H)).inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem mem_localNormalizer_of_normalizes [Finite H] {p : ℕ} [Fact p.Prime] {T L : Subgroup H}
    (hS : IsSylowOf p (T ⊓ L) L) {g : H} (hgL : g ∈ L)
    (hg : g ∈ Subgroup.normalizer (localNormalizer T L : Set H)) : g ∈ localNormalizer T L := by
  have hUB : T ⊓ L ≤ localNormalizer T L := inf_le_localNormalizer T L
  have hSB : IsSylowOf p (T ⊓ L) (localNormalizer T L) := hS.of_le hUB (localNormalizer_le T L)
  obtain ⟨Q, hQ⟩ := hSB.exists_sylow_eq_subgroupOf
  have hn : ((T ⊓ L).subgroupOf (localNormalizer T L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).2 inf_le_left
  exact ⟨conj_normalizes_of_normal_sylow Q hQ hUB hn hg, hgL⟩

theorem conj_noncommPiCoprod_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → Subgroup H)
    (hcomm : Pairwise fun i j => ∀ x y : H, x ∈ L i → y ∈ L j → Commute x y)
    (x : ∀ i, L i) (i : ι) {y : H} (hy : y ∈ L i) :
    Subgroup.noncommPiCoprod hcomm x * y * (Subgroup.noncommPiCoprod hcomm x)⁻¹ =
      (x i : H) * y * (x i : H)⁻¹ := by
  have hc := commute_noncommPiCoprod_update L hcomm x i hy
  rw [noncommPiCoprod_eq_mul_update L hcomm x i, mul_inv_rev]
  calc (x i : H) * Subgroup.noncommPiCoprod hcomm (Function.update x i 1) * y *
        ((Subgroup.noncommPiCoprod hcomm (Function.update x i 1))⁻¹ * (x i : H)⁻¹)
      = (x i : H) * (Subgroup.noncommPiCoprod hcomm (Function.update x i 1) * y *
        (Subgroup.noncommPiCoprod hcomm (Function.update x i 1))⁻¹) * (x i : H)⁻¹ := by group
    _ = (x i : H) * y * (x i : H)⁻¹ := by rw [← hc.eq, mul_inv_cancel_right]

theorem transitive_direct_product_local_sylow_normalizers [Finite H]
    {p : ℕ} [Fact p.Prime] {T M K : Subgroup H} (hT : IsSylowOf p T ⊤) (hTM : T ≤ M)
    (hMH : M < ⊤) (hmax : ∀ Y : Subgroup H, T ≤ Y → Y < ⊤ → Y ≤ M)
    {r : ℕ} (hr : 1 ≤ r) {L : Fin r → Subgroup H} (hKn : K.Normal) (hK : K = ⨆ i, L i)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hind : ∀ i, L i ⊓ (⨆ j, ⨆ (_ : j ≠ i), L j) = ⊥) (hKT : K ⊔ T = ⊤)
    (htrans : ∀ i j, ∃ t ∈ T, (L i).map (MulAut.conj t).toMonoidHom = L j)
    (hBmax : ∀ i, localNormalizer T (L i) < L i ∧ ∀ Y : Subgroup H,
      localNormalizer T (L i) ≤ Y → Y ≤ L i → Y = localNormalizer T (L i) ∨ Y = L i) :
    (∀ i, IsSylowOf p (T ⊓ L i) (L i)) ∧ T ⊓ K = ⨆ i, T ⊓ L i ∧
      M = Subgroup.normalizer ((T ⊓ K : Subgroup H) : Set H) ∧
      M = (⨆ i, localNormalizer T (L i)) ⊔ T ∧ M ⊓ K = ⨆ i, localNormalizer T (L i) ∧
      (∀ i, M ⊓ L i = localNormalizer T (L i)) ∧ Subgroup.normalizer (T : Set H) ≤ M ∧
      M.index = ∏ i, (localNormalizer T (L i)).relIndex (L i) := by
  classical
  have hLK : ∀ i, L i ≤ K := fun i => hK ▸ le_iSup L i
  have hcommP : Pairwise fun i j => ∀ x y : H, x ∈ L i → y ∈ L j → Commute x y :=
    fun i j hij x y hx hy => hcomm i j hij x hx y hy
  have hindL : iSupIndep L := iSupIndep_def.2 fun i => disjoint_iff.2 (hind i)
  have hKnorm : ∀ i, K ≤ Subgroup.normalizer (L i : Set H) := by
    intro i
    rw [hK]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst hji; exact Subgroup.le_normalizer
    · have : L j ≤ Subgroup.centralizer (L i : Set H) := fun x hx =>
        Subgroup.mem_centralizer_iff.2 fun z hz => (hcomm j i hji x hx z hz).symm
      exact this.trans (Subgroup.centralizer_le_normalizer _)
  have hTK : T ≤ Subgroup.normalizer (K : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hKn]; exact le_top
  have hD : IsSylowOf p (T ⊓ K) K :=
    hT.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.2 hKn])
  have hU : ∀ i, IsSylowOf p (T ⊓ L i) (L i) := by
    intro i
    have := hD.inf_of_le_normalizer (hLK i) (hKnorm i)
    rwa [inf_assoc, inf_eq_right.2 (hLK i)] at this
  have hDL : ∀ i, (T ⊓ K) ⊓ L i = T ⊓ L i := fun i => by
    rw [inf_assoc, inf_eq_right.2 (hLK i)]
  have hDeq : T ⊓ K = ⨆ i, T ⊓ L i := by
    have hle : (⨆ i, T ⊓ L i) ≤ T ⊓ K := iSup_le fun i => inf_le_inf_left T (hLK i)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have hcommU : Pairwise fun i j => ∀ x y : H, x ∈ T ⊓ L i → y ∈ T ⊓ L j → Commute x y :=
      fun i j hij x y hx hy => hcomm i j hij x hx.2 y hy.2
    have hindU : iSupIndep fun i => T ⊓ L i := by
      rw [iSupIndep_def]
      intro i
      rw [disjoint_iff, eq_bot_iff, ← hind i]
      exact inf_le_inf inf_le_right (iSup₂_mono fun j _ => inf_le_right)
    have hK_card : Nat.card ↥K = ∏ i, Nat.card ↥(L i) := by
      rw [hK]; exact natCard_iSup_eq_prod L hcommP hindL
    rw [natCard_iSup_eq_prod _ hcommU hindU, hD.card_eq, hK_card,
      Nat.factorization_prod (fun i _ => Nat.card_pos.ne'), Finsupp.finsetSum_apply,
      ← Finset.prod_pow_eq_pow_sum]
    exact le_of_eq (Finset.prod_congr rfl fun i _ => (hU i).card_eq.symm)
  have hBL : ∀ i, localNormalizer T (L i) ≤ L i := fun i => localNormalizer_le T (L i)
  have hBN : ∀ i, localNormalizer T (L i) ≤
      Subgroup.normalizer ((T ⊓ K : Subgroup H) : Set H) := by
    intro i b hb
    rw [hDeq]
    refine mem_normalizer_iSup _ fun j => ?_
    by_cases hji : j = i
    · subst hji; exact hb.1
    · have hbc : b ∈ Subgroup.centralizer ((T ⊓ L j : Subgroup H) : Set H) :=
        Subgroup.mem_centralizer_iff.2 fun x hx => (hcomm i j (Ne.symm hji) b (hBL i hb) x hx.2).symm
      exact Subgroup.centralizer_le_normalizer _ hbc
  have hTN : T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup H) : Set H) := fun t ht =>
    mem_normalizer_inf (Subgroup.le_normalizer ht) (hTK ht)
  have hNtop : Subgroup.normalizer ((T ⊓ K : Subgroup H) : Set H) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hN => ?_
    obtain i : Fin r := ⟨0, hr⟩
    have hle : L i ≤ localNormalizer T (L i) := by
      intro x hx
      refine ⟨?_, hx⟩
      have h1 : x ∈ Subgroup.normalizer ((T ⊓ K : Subgroup H) : Set H) := by rw [hN]; trivial
      have h2 := mem_normalizer_inf h1 (hKnorm i (hLK i hx))
      rwa [hDL i] at h2
    exact absurd (lt_of_le_of_lt hle (hBmax i).1) (lt_irrefl _)
  have hNM : Subgroup.normalizer ((T ⊓ K : Subgroup H) : Set H) ≤ M := hmax _ hTN hNtop
  have hBM : ∀ i, localNormalizer T (L i) ≤ M := fun i => (hBN i).trans hNM
  have hLM : ∀ i, ¬ L i ≤ M := by
    intro i hi
    have hall : ∀ j, L j ≤ M := by
      intro j
      obtain ⟨t, ht, hj⟩ := htrans i j
      rw [← hj]
      rintro _ ⟨x, hx, rfl⟩
      exact M.mul_mem (M.mul_mem (hTM ht) (hi hx)) (M.inv_mem (hTM ht))
    have hKM : K ≤ M := by rw [hK]; exact iSup_le hall
    have : (⊤ : Subgroup H) ≤ M := by rw [← hKT]; exact sup_le hKM hTM
    exact absurd hMH (not_lt_of_ge this)
  have hML : ∀ i, M ⊓ L i = localNormalizer T (L i) := by
    intro i
    rcases (hBmax i).2 (M ⊓ L i) (le_inf (hBM i) (hBL i)) inf_le_right with h | h
    · exact h
    · exact absurd (h ▸ inf_le_left) (hLM i)
  have hcoord : ∀ k ∈ K, (∀ i, k ∈ Subgroup.normalizer (localNormalizer T (L i) : Set H)) →
      k ∈ ⨆ i, localNormalizer T (L i) := by
    intro k hkK hk
    have hkr : k ∈ (Subgroup.noncommPiCoprod hcommP).range := by
      rw [Subgroup.noncommPiCoprod_range, ← hK]; exact hkK
    obtain ⟨x, rfl⟩ := hkr
    rw [Subgroup.noncommPiCoprod_apply]
    refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
    refine le_iSup (fun j => localNormalizer T (L j)) i ?_
    refine mem_localNormalizer_of_normalizes (hU i) (x i).2 ?_
    refine mem_normalizer_of_forall_mem (fun z hz => ?_) (fun z hz => ?_)
    · rw [← conj_noncommPiCoprod_eq L hcommP x i (hBL i hz)]
      exact (Subgroup.mem_normalizer_iff.1 (hk i) z).1 hz
    · have h := conj_noncommPiCoprod_eq L hcommP x⁻¹ i (hBL i hz)
      rw [map_inv] at h
      simp only [Pi.inv_apply, Subgroup.coe_inv, inv_inv] at h
      rw [← h]
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem (hk i)) z).1 hz
      simpa using this
  have hMK : M ⊓ K = ⨆ i, localNormalizer T (L i) := by
    apply le_antisymm
    · rintro k ⟨hkM, hkK⟩
      refine hcoord k hkK fun i => ?_
      have h1 : k ∈ Subgroup.normalizer ((M ⊓ L i : Subgroup H) : Set H) :=
        mem_normalizer_inf (Subgroup.le_normalizer hkM) (hKnorm i hkK)
      rwa [hML i] at h1
    · exact le_inf (iSup_le hBM) (iSup_le fun i => (hBL i).trans (hLK i))
  have hMN : M = Subgroup.normalizer ((T ⊓ K : Subgroup H) : Set H) := by
    refine le_antisymm (fun m hm => ?_) hNM
    obtain ⟨k, hk, t, ht, rfl⟩ := mem_sup_mul hTK (show m ∈ K ⊔ T by rw [hKT]; trivial)
    have hkM : k ∈ M := by
      have := M.mul_mem hm (M.inv_mem (hTM ht))
      simpa using this
    have hkB : k ∈ ⨆ i, localNormalizer T (L i) := by
      have : k ∈ M ⊓ K := ⟨hkM, hk⟩
      rwa [hMK] at this
    exact Subgroup.mul_mem _ (iSup_le hBN hkB) (hTN ht)
  have hMT : M = (⨆ i, localNormalizer T (L i)) ⊔ T := by
    refine le_antisymm (fun m hm => ?_) (sup_le (iSup_le hBM) hTM)
    obtain ⟨k, hk, t, ht, rfl⟩ := mem_sup_mul hTK (show m ∈ K ⊔ T by rw [hKT]; trivial)
    have hkM : k ∈ M := by
      have := M.mul_mem hm (M.inv_mem (hTM ht))
      simpa using this
    have hkB : k ∈ ⨆ i, localNormalizer T (L i) := by
      have : k ∈ M ⊓ K := ⟨hkM, hk⟩
      rwa [hMK] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hkB) (Subgroup.mem_sup_right ht)
  have hNT : Subgroup.normalizer (T : Set H) ≤ M := by
    intro n hn
    rw [hMN]
    exact mem_normalizer_inf hn ((by rw [Subgroup.normalizer_eq_top_iff.2 hKn]; trivial))
  refine ⟨hU, hDeq, hMN, hMT, hMK, hML, hNT, ?_⟩
  have hMsup : M ⊔ K = ⊤ := by
    rw [eq_top_iff, ← hKT]
    exact sup_le le_sup_right (hTM.trans le_sup_left) |>.trans le_rfl
  have hMnorm : M ≤ Subgroup.normalizer (K : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hKn]; exact le_top
  have h1 : (M ⊓ K).relIndex K = M.index := by
    rw [relIndex_inf_eq_relIndex_sup hMnorm, hMsup, Subgroup.relIndex_top_right]
  rw [← h1, hMK]
  have hcommB : Pairwise fun i j => ∀ x y : H, x ∈ localNormalizer T (L i) →
      y ∈ localNormalizer T (L j) → Commute x y :=
    fun i j hij x y hx hy => hcomm i j hij x (hBL i hx) y (hBL j hy)
  have hindB : iSupIndep fun i => localNormalizer T (L i) := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, eq_bot_iff, ← hind i]
    exact inf_le_inf (hBL i) (iSup₂_mono fun j _ => hBL j)
  have hK_card : Nat.card ↥K = ∏ i, Nat.card ↥(L i) := by
    rw [hK]; exact natCard_iSup_eq_prod L hcommP hindL
  have hB_card := natCard_iSup_eq_prod (fun i => localNormalizer T (L i)) hcommB hindB
  have e1 := Subgroup.relIndex_mul_card (⨆ i, localNormalizer T (L i)) K
  rw [inf_eq_left.2 (iSup_le fun i => (hBL i).trans (hLK i)), hB_card, hK_card] at e1
  have e2 : ∀ i, (localNormalizer T (L i)).relIndex (L i) * Nat.card ↥(localNormalizer T (L i)) =
      Nat.card ↥(L i) := fun i => by
    have := Subgroup.relIndex_mul_card (localNormalizer T (L i)) (L i)
    rwa [inf_eq_left.2 (hBL i)] at this
  have e3 : (∏ i, (localNormalizer T (L i)).relIndex (L i)) * ∏ i, Nat.card ↥(localNormalizer T (L i)) =
      ∏ i, Nat.card ↥(L i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => e2 i
  have hpos : 0 < ∏ i, Nat.card ↥(localNormalizer T (L i)) :=
    Finset.prod_pos fun i _ => Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (e1.trans e3.symm)

end CFSG.QuasithinUnique.Setup.Lift
