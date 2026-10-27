module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.HardMathSupport.Timmesfeld.Proving.CommutingProduct
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FamilyCard
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open

variable {G : Type*} [Group G] {p : ℕ}

theorem isElemAbelian_comm {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem isElemAbelian_pow_eq_one {E : Subgroup G} (hE : IsElemAbelian p E) {a : G} (ha : a ∈ E) :
    a ^ p = 1 :=
  hE.2 a ha

theorem isElemAbelian_of_forall {E : Subgroup G} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hp : ∀ x ∈ E, x ^ p = 1) : IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩

theorem isElemAbelian_mono {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem mem_sup_iff_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} : x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  constructor
  · intro hx
    have hrange : (Proving.mulOfCommute A B hc).range = A ⊔ B := by
      apply le_antisymm
      · intro y hy
        obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hy
        rw [Proving.mulOfCommute_apply]
        exact mul_mem (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)
      · apply sup_le
        · intro a ha
          exact MonoidHom.mem_range.mpr ⟨(⟨a, ha⟩, 1), by simp [Proving.mulOfCommute_apply]⟩
        · intro b hb
          exact MonoidHom.mem_range.mpr ⟨(1, ⟨b, hb⟩), by simp [Proving.mulOfCommute_apply]⟩
    rw [← hrange] at hx
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨q.1, q.1.2, q.2, q.2.2, Proving.mulOfCommute_apply A B hc q⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem isElemAbelian_sup_of_commute {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian p (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hc

theorem isElemAbelian_exists_card_eq_pow [Finite G] (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) : ∃ n : ℕ, Nat.card E = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using isElemAbelian_pow_eq_one hE g.2⟩
  exact (IsPGroup.iff_card).1 hP

theorem isElemAbelian_card_le_pow [Finite G] (hp : p.Prime) {W Zk : Subgroup G}
    (hW : IsElemAbelian p W) (hWZ : W ≤ Zk) {z : ℕ} (hz : pRank p Zk ≤ z) :
    Nat.card W ≤ p ^ z := by
  obtain ⟨n, hn⟩ := isElemAbelian_exists_card_eq_pow hp hW
  have hnz : n ≤ z := (CFSG.SectionRank.le_pRank hp.one_lt hWZ hW hn).trans hz
  rw [hn]
  exact Nat.pow_le_pow_right hp.pos hnz

theorem card_mul_le_card_sup_mul_pow [Finite G] (hp : p.Prime) {A B W : Subgroup G}
    (hA : IsElemAbelian p A) (hB : IsElemAbelian p B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hW : A ⊓ B ≤ W) {s : ℕ} (hs : pRank p W ≤ s) :
    IsElemAbelian p (A ⊔ B) ∧ Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) * p ^ s := by
  refine ⟨isElemAbelian_sup_of_commute hA hB hc, ?_⟩
  have hint : IsElemAbelian p (A ⊓ B) := isElemAbelian_mono hA inf_le_left
  have h1 := Proving.card_sup_mul_card_inf A B hc
  have h2 : Nat.card ↥(A ⊓ B) ≤ p ^ s := isElemAbelian_card_le_pow hp hint hW hs
  calc Nat.card A * Nat.card B = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) :=
        h1.symm
    _ ≤ Nat.card ↥(A ⊔ B) * p ^ s := Nat.mul_le_mul_left _ h2


variable {ι : Type*} {L : ι → Subgroup G}

theorem CommFam.exists_elemAbelian_card_mul_le [Fintype ι] [DecidableEq ι] [Finite G]
    (h : CommFam L) (hp : p.Prime) {z : ℕ} (hz : ∀ k, pRank p (centreIn (L k)) ≤ z)
    {E₀ : Subgroup G} (hE₀ : E₀ ≤ Subgroup.centralizer ((⨆ i, L i : Subgroup G) : Set G))
    (hE₀a : IsElemAbelian p E₀) (E : ι → Subgroup G) (hEL : ∀ k, E k ≤ L k)
    (hEa : ∀ k, IsElemAbelian p (E k)) :
    ∃ F : Subgroup G, F ≤ E₀ ⊔ ⨆ k, E k ∧ IsElemAbelian p F ∧
      Nat.card E₀ * ∏ k, Nat.card (E k) ≤ Nat.card F * p ^ (Fintype.card ι * z) := by
  have key : ∀ s : Finset ι, ∃ F : Subgroup G, F ≤ E₀ ⊔ ⨆ k ∈ s, E k ∧ IsElemAbelian p F ∧
      Nat.card E₀ * ∏ k ∈ s, Nat.card (E k) ≤ Nat.card F * p ^ (s.card * z) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨E₀, le_sup_left, hE₀a, ?_⟩
      simp
    | insert k s hks ih =>
      obtain ⟨F, hFle, hFa, hFcard⟩ := ih
      have hFc : F ≤ Subgroup.centralizer (L k : Set G) := by
        refine hFle.trans (sup_le ?_ ?_)
        · intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          exact Subgroup.mem_centralizer_iff.1 (hE₀ hx) g (le_iSup L k hg)
        · refine iSup₂_le fun j hj => ?_
          have hjk : j ≠ k := fun hjk => hks (hjk ▸ hj)
          exact (hEL j).trans (h.le_centralizer hjk)
      have hc : ∀ a ∈ F, ∀ b ∈ E k, a * b = b * a := fun a ha b hb =>
        (Subgroup.mem_centralizer_iff.1 (hFc ha) b (hEL k hb)).symm
      have hW : F ⊓ E k ≤ centreIn (L k) := by
        intro x hx
        obtain ⟨hxF, hxE⟩ := Subgroup.mem_inf.1 hx
        exact mem_centreIn.2 ⟨hEL k hxE, fun g hg =>
          Subgroup.mem_centralizer_iff.1 (hFc hxF) g hg⟩
      obtain ⟨hFEa, hstep⟩ := card_mul_le_card_sup_mul_pow hp hFa (hEa k) hc hW (hz k)
      refine ⟨F ⊔ E k, ?_, hFEa, ?_⟩
      · refine sup_le (hFle.trans ?_) ?_
        · have hmono : (⨆ j ∈ s, E j) ≤ ⨆ j ∈ insert k s, E j :=
            iSup₂_mono' fun j hj => ⟨j, Finset.mem_insert_of_mem hj, le_rfl⟩
          exact sup_le_sup_left hmono E₀
        · exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ∈ insert k s) => E j) k
            (Finset.mem_insert_self k s))
      · rw [Finset.prod_insert hks, Finset.card_insert_of_notMem hks, Nat.succ_mul, pow_add]
        calc Nat.card E₀ * (Nat.card (E k) * ∏ j ∈ s, Nat.card (E j))
            = Nat.card (E k) * (Nat.card E₀ * ∏ j ∈ s, Nat.card (E j)) := by ring
          _ ≤ Nat.card (E k) * (Nat.card F * p ^ (s.card * z)) := Nat.mul_le_mul_left _ hFcard
          _ = (Nat.card F * Nat.card (E k)) * p ^ (s.card * z) := by ring
          _ ≤ (Nat.card ↥(F ⊔ E k) * p ^ z) * p ^ (s.card * z) :=
              Nat.mul_le_mul_right _ hstep
          _ = Nat.card ↥(F ⊔ E k) * (p ^ (s.card * z) * p ^ z) := by ring
  obtain ⟨F, hFle, hFa, hFcard⟩ := key Finset.univ
  refine ⟨F, ?_, hFa, ?_⟩
  · exact hFle.trans (sup_le_sup_left (iSup₂_le fun k _ => le_iSup E k) E₀)
  · rwa [Finset.card_univ] at hFcard

theorem CommFam.exists_elemAbelian_rank_le [Fintype ι] [DecidableEq ι] [Finite G]
    (h : CommFam L) (hp : p.Prime) {z : ℕ} (hz : ∀ k, pRank p (centreIn (L k)) ≤ z)
    {E₀ : Subgroup G} (hE₀ : E₀ ≤ Subgroup.centralizer ((⨆ i, L i : Subgroup G) : Set G))
    (hE₀a : IsElemAbelian p E₀) (E : ι → Subgroup G) (hEL : ∀ k, E k ≤ L k)
    (hEa : ∀ k, IsElemAbelian p (E k)) {e₀ : ℕ} (he₀ : Nat.card E₀ = p ^ e₀) {e : ι → ℕ}
    (he : ∀ k, Nat.card (E k) = p ^ e k) :
    ∃ F : Subgroup G, F ≤ E₀ ⊔ ⨆ k, E k ∧ IsElemAbelian p F ∧
      ∃ f : ℕ, Nat.card F = p ^ f ∧ e₀ + ∑ k, e k ≤ f + Fintype.card ι * z := by
  obtain ⟨F, hFle, hFa, hF⟩ := h.exists_elemAbelian_card_mul_le hp hz hE₀ hE₀a E hEL hEa
  obtain ⟨f, hf⟩ := isElemAbelian_exists_card_eq_pow hp hFa
  refine ⟨F, hFle, hFa, f, hf, ?_⟩
  rw [he₀, hf] at hF
  simp only [he, Finset.prod_pow_eq_pow_sum] at hF
  rw [← pow_add, ← pow_add] at hF
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hF

theorem CommFam.le_pRank_add_card_mul [Fintype ι] [DecidableEq ι] [Finite G]
    (h : CommFam L) (hp : p.Prime) {z : ℕ} (hz : ∀ k, pRank p (centreIn (L k)) ≤ z)
    {E₀ : Subgroup G} (hE₀ : E₀ ≤ Subgroup.centralizer ((⨆ i, L i : Subgroup G) : Set G))
    (hE₀a : IsElemAbelian p E₀) (E : ι → Subgroup G) (hEL : ∀ k, E k ≤ L k)
    (hEa : ∀ k, IsElemAbelian p (E k)) {e₀ : ℕ} (he₀ : Nat.card E₀ = p ^ e₀) {e : ι → ℕ}
    (he : ∀ k, Nat.card (E k) = p ^ e k) {H : Subgroup G} (hH : E₀ ⊔ ⨆ k, E k ≤ H) :
    e₀ + ∑ k, e k ≤ pRank p H + Fintype.card ι * z := by
  obtain ⟨F, hFle, hFa, f, hf, hle⟩ := h.exists_elemAbelian_rank_le hp hz hE₀ hE₀a E hEL hEa he₀ he
  have : f ≤ pRank p H := CFSG.SectionRank.le_pRank hp.one_lt (hFle.trans hH) hFa hf
  omega

theorem CommFam.isElemAbelian_iSup [Fintype ι] [DecidableEq ι] {E : ι → Subgroup G}
    (h : CommFam E) (hEa : ∀ k, IsElemAbelian p (E k)) : IsElemAbelian p (⨆ k, E k) := by
  rw [← range_famProd h]
  refine isElemAbelian_of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
  · obtain ⟨f, rfl⟩ := ha
    obtain ⟨g, rfl⟩ := hb
    rw [← map_mul, ← map_mul]
    congr 1
    funext k
    exact Subtype.ext (isElemAbelian_comm (hEa k) (f k).2 (g k).2)
  · obtain ⟨f, rfl⟩ := ha
    rw [← map_pow]
    have : f ^ p = 1 := by
      funext k
      exact Subtype.ext (isElemAbelian_pow_eq_one (hEa k) (f k).2)
    rw [this, map_one]

theorem CommFam.isElemAbelian_card_iSup_of_iSupIndep [Fintype ι] [DecidableEq ι] [Finite G]
    (h : CommFam L) (hind : iSupIndep L) (E : ι → Subgroup G) (hEL : ∀ k, E k ≤ L k)
    (hEa : ∀ k, IsElemAbelian p (E k)) {e : ι → ℕ} (he : ∀ k, Nat.card (E k) = p ^ e k) :
    IsElemAbelian p (⨆ k, E k) ∧ Nat.card ↥(⨆ k, E k) = p ^ ∑ k, e k := by
  have hE : CommFam E := fun _ _ hij x y hx hy => h hij x y (hEL _ hx) (hEL _ hy)
  refine ⟨hE.isElemAbelian_iSup hEa, ?_⟩
  rw [h.card_iSup_eq_prod_of_le hind E hEL]
  simp only [he, Finset.prod_pow_eq_pow_sum]

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance

end
