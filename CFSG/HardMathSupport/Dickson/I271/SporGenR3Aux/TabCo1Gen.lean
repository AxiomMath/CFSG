module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeMulti

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4

section Product

variable {Q : Type} [Group Q]

theorem conj_mem_zpowers_sup {g : Q} {L : Subgroup Q} (hcomm : ∀ l ∈ L, l * g = g * l) :
    ∀ h ∈ Subgroup.zpowers g ⊔ L, ∀ l ∈ L, h * l * h⁻¹ ∈ L := by
  have hg : g ∈ Subgroup.normalizer (L : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have : g * n * g⁻¹ = n := by rw [← hcomm n hn]; group
      rwa [this]
    · intro hn
      have h1 : g⁻¹ * (g * n * g⁻¹) * g = n := by group
      have h2 : g⁻¹ * (g * n * g⁻¹) * g = g * n * g⁻¹ := by
        have : (g * n * g⁻¹) * g = g * (g * n * g⁻¹) := hcomm _ hn
        rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [← h1, h2]
      exact hn
  have hle : Subgroup.zpowers g ⊔ L ≤ Subgroup.normalizer (L : Set Q) :=
    sup_le (Subgroup.zpowers_le.2 hg) Subgroup.le_normalizer
  intro h hh l hl
  exact (Subgroup.mem_normalizer_iff.1 (hle hh) l).1 hl

theorem le_card_zpowers_sup {p : ℕ} (hp : p.Prime) {g : Q} (hg : orderOf g = p) {L : Subgroup Q}
    [Finite ↥(Subgroup.zpowers g ⊔ L)] (hcomm : ∀ l ∈ L, l * g = g * l)
    (hZ : ∀ l ∈ L, (∀ m ∈ L, m * l = l * m) → l = 1) :
    p * Nat.card ↥L ≤ Nat.card ↥(Subgroup.zpowers g ⊔ L) := by
  set H : Subgroup Q := Subgroup.zpowers g ⊔ L with hH
  have hLH : L ≤ H := le_sup_right
  have hgH : g ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
  let N : Subgroup ↥H := L.subgroupOf H
  have h1 : Nat.card ↥H = Nat.card (↥H ⧸ N) * Nat.card ↥N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h2 : Nat.card ↥N = Nat.card ↥L := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv
  let gH : ↥H := ⟨g, hgH⟩
  have hne : ∀ i j : ℕ, i < j → j < p →
      (QuotientGroup.mk (gH ^ i) : ↥H ⧸ N) ≠ QuotientGroup.mk (gH ^ j) := by
    intro i j hij hjp heq
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at heq
    have hm : g ^ (j - i) ∈ L := by
      have e : ((gH ^ i)⁻¹ * gH ^ j : ↥H) = gH ^ (j - i) := by
        have : gH ^ j = gH ^ i * gH ^ (j - i) := by rw [← pow_add]; congr 1; omega
        rw [this, inv_mul_cancel_left]
      have := heq
      rw [e] at this
      simpa using this
    have hcomm' : ∀ m ∈ L, m * g ^ (j - i) = g ^ (j - i) * m := fun m hm' =>
      (Commute.pow_right (show Commute m g from hcomm m hm') (j - i)).eq
    have h1' : g ^ (j - i) = 1 := hZ _ hm hcomm'
    have : p ∣ j - i := hg ▸ orderOf_dvd_of_pow_eq_one h1'
    have := Nat.le_of_dvd (by omega) this
    omega
  have hinj : Function.Injective (fun i : Fin p => (QuotientGroup.mk (gH ^ (i : ℕ)) : ↥H ⧸ N)) := by
    intro i j hij
    by_contra hne'
    rcases lt_or_gt_of_ne (fun h => hne' (Fin.ext h)) with h | h
    · exact hne i j h j.2 hij
    · exact hne j i h i.2 hij.symm
  have h3 : p ≤ Nat.card (↥H ⧸ N) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  calc p * Nat.card ↥L ≤ Nat.card (↥H ⧸ N) * Nat.card ↥L := Nat.mul_le_mul_right _ h3
    _ = Nat.card ↥H := by rw [h1, h2]

end Product

section Shape

variable {Q : Type} [Group Q]

theorem multiShapeAt_of_shapeRkAt {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    {k : Q} (h : ShapeRkAt p Good Rk k) : MultiShapeAt p Good Rk k := by
  rcases h with hc | ⟨J, hJ, hu, hG, hR⟩
  · exact Or.inl hc
  · refine Or.inr ⟨[J], by simpa using hp.one_lt, fun I hI => ?_, fun I hI => ?_⟩
    · rw [hu I hI]; simp
    · rw [hu I hI]; exact ⟨hG, hR⟩

theorem atMostOneCompAt_of_shapeRkAt [Finite Q] {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop} {k : Q} (h : ShapeRkAt p Good Rk k) :
    AtMostOneCompAt p k := by
  rcases h with hc | ⟨J, hJ, hu, hG, hR⟩
  · intro I J' hI _
    exact (no_glaPComponent_of_pConstrainedShape hp hc hI).elim
  · intro I J' hI hJ'
    rw [hu I hI, hu J' hJ']

theorem atMostOneCompAt_of_pConstrained [Finite Q] {p : ℕ} (hp : p.Prime) {k : Q}
    (hc : PConstrainedShape p (Subgroup.centralizer ({k} : Set Q))) : AtMostOneCompAt p k :=
  fun _ _ hI _ => (no_glaPComponent_of_pConstrainedShape hp hc hI).elim

end Shape

section Bound

variable {G : Type} [Group G]

theorem shapeRkAt_of_bound {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (P : Subgroup G) [Finite P] (x : ↥P) (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P)
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    (hx1 : (x : G) ≠ 1) (hxp : (x : G) ^ p = 1)
    (hbound : Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ P) ≤ p * Nat.card ↥L)
    (hG : Good ↥L) (hR : Rk ↥L) : ShapeRkAt p Good Rk x := by
  have hLP : L ≤ P := fun l hl => (hLC hl).2
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (x : G) = p := orderOf_eq_prime hxp hx1
  set C : Subgroup G := Subgroup.centralizer ({(x : G)} : Set G) ⊓ P with hC
  have hgC : (x : G) ∈ C := ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, x.2⟩
  have hKL : Subgroup.zpowers (x : G) ⊔ L ≤ C := sup_le (Subgroup.zpowers_le.2 hgC) hLC
  have hCP : C ≤ P := inf_le_right
  haveI : Finite ↥C :=
    Finite.of_injective (Subgroup.inclusion hCP) (Subgroup.inclusion_injective hCP)
  haveI : Finite ↥(Subgroup.zpowers (x : G) ⊔ L) :=
    Finite.of_injective (Subgroup.inclusion hKL) (Subgroup.inclusion_injective hKL)
  haveI := hs
  have hcomm : ∀ l ∈ L, l * (x : G) = (x : G) * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hLC hl).1
  have hZ : ∀ l ∈ L, (∀ m ∈ L, m * l = l * m) → l = 1 := by
    intro l hl hm
    have hmem : (⟨l, hl⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hm b b.2)
    rw [center_eq_bot_of_simple_nonab hnab, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have h1 := le_card_zpowers_sup hp hord hcomm hZ
  have h2 : Nat.card ↥(Subgroup.zpowers (x : G) ⊔ L) ≤ Nat.card ↥C := Subgroup.card_le_of_le hKL
  have hKC : Subgroup.zpowers (x : G) ⊔ L = C :=
    Subgroup.eq_of_le_of_card_ge hKL (by omega)
  have hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    rw [← hKC]
    exact conj_mem_zpowers_sup hcomm
  have hk : Nat.card ↥C = Nat.card ↥L * p ^ 1 := by
    rw [pow_one, mul_comm]
    omega
  exact shapeRkAt_of_subgroup_data hp hGood hRk P x L hLC hLn hs hnab hpL hk hG hR

end Bound

end CFSG.HardMathSupport.Dickson.I271
