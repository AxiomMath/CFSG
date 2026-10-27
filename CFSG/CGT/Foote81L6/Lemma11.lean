module

public import CFSG.CGT.Foote81L6.Swap
public import CFSG.CGT.Foote81L6.T0Sylow
public import CFSG.CGT.Foote81L6.Normalizer.Lemma11Core
public import CFSG.CGT.Foote81L6.E64Fix
public import CFSG.CGT.Foote81L6.NBar
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.Foote81L6

open Subgroup CFSG.Quasithin
open scoped IsMulCommutative

theorem commV_zpowers_invariant {V : Type*} [CommGroup V] {g y : MulAut V} (hgy : g * y = y * g)
    {u : V} (hu : u ∈ commV (zpowers y)) : g u ∈ commV (zpowers y) := by
  have hle : (commV (zpowers y)).map g.toMonoidHom ≤ commV (zpowers y) := by
    rw [commV, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨z, hz, v, rfl⟩, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
    have hc : g * y ^ k = y ^ k * g := (Commute.zpow_right hgy k).eq
    refine subset_closure ⟨y ^ k, zpow_mem (mem_zpowers y) k, g v, ?_⟩
    show (y ^ k) (g v) * (g v)⁻¹ = g ((y ^ k) v * v⁻¹)
    rw [map_mul, map_inv, ← MulAut.mul_apply, ← hc, MulAut.mul_apply]
  exact hle ⟨u, hu, rfl⟩

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {n : ℕ} (D : FooteCore G T 2 n)

theorem mem_zpowers_a_iff_gen {m : ℕ} (D : FooteCore G T m n) {x : G} :
    x ∈ zpowers D.a ↔ x = 1 ∨ x = D.a := by
  constructor
  · intro hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hx
    rw [zpow_eq_zpow_emod' j (show D.a ^ 2 = 1 by rw [sq]; exact D.a_mul_a)]
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
    · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem mem_A_of_two {a₁ x : G} (ha₁ : a₁ ∈ D.A) (ha₁1 : a₁ ≠ 1) (ha₁a : a₁ ≠ D.a)
    (hx : x ∈ D.A) : x = 1 ∨ x = D.a ∨ x = a₁ ∨ x = D.a * a₁ := by
  haveI := D.finite_A
  by_cases hxa : x ∈ zpowers D.a
  · rcases (mem_zpowers_a_iff_gen D).1 hxa with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have ha₁Z : a₁ ∉ zpowers D.a := fun h => by
      rcases (mem_zpowers_a_iff_gen D).1 h with h | h
      · exact ha₁1 h
      · exact ha₁a h
    have hle : zpowers D.a ≤ D.A := zpowers_le.2 D.a_mem
    have hcard : Nat.card D.A = 2 * Nat.card (zpowers D.a) := by
      rw [D.card_A, Nat.card_zpowers, D.a_order]
      norm_num
    have h := inv_mul_mem_of_card_eq_two_mul hle hcard ha₁ hx ha₁Z hxa
    rcases (mem_zpowers_a_iff_gen D).1 h with h | h
    · exact Or.inr (Or.inr (Or.inl (inv_mul_eq_one.1 h).symm))
    · right; right; right
      have : x = a₁ * D.a := by rw [← h]; group
      rw [this, D.A_comm_of_two ha₁ D.a_mem]

theorem b₀_comm_T₁ {g : G} (hg : g ∈ D.T₁) : g * D.b₀ = D.b₀ * g := by
  have hle : D.T₁ ≤ centralizer ({D.b₀} : Set G) := sup_le
    (fun x hx => mem_centralizer_singleton_iff.2 (D.A_comm_B x hx D.b₀ D.b₀_mem_B))
    (sup_le (fun x hx => mem_centralizer_singleton_iff.2 (D.b₀_comm x hx))
      (fun x hx => mem_centralizer_singleton_iff.2 (D.B₀_comm_B₁ D.b₀ D.b₀_mem x hx).symm))
  exact mem_centralizer_singleton_iff.1 (hle hg)

theorem b₁_comm_T₁ {g : G} (hg : g ∈ D.T₁) : g * D.b₁ = D.b₁ * g := by
  have hle : D.T₁ ≤ centralizer ({D.b₁} : Set G) := sup_le
    (fun x hx => mem_centralizer_singleton_iff.2 (D.A_comm_B x hx D.b₁ D.b₁_mem_B))
    (sup_le (fun x hx => mem_centralizer_singleton_iff.2 (D.B₀_comm_B₁ x hx D.b₁ D.b₁_mem))
      (fun x hx => mem_centralizer_singleton_iff.2 (D.b₁_comm x hx)))
  exact mem_centralizer_singleton_iff.1 (hle hg)

theorem A_comm_T₁ {g x : G} (hg : g ∈ D.T₁) (hx : x ∈ D.A) : g * x = x * g := by
  have hle : D.T₁ ≤ centralizer ({x} : Set G) := sup_le
    (fun y hy => mem_centralizer_singleton_iff.2 (D.A_comm_of_two hy hx))
    (fun y hy => mem_centralizer_singleton_iff.2 (D.A_comm_B x hx y (D.B₀B₁_le_B hy)).symm)
  exact mem_centralizer_singleton_iff.1 (hle hg)

theorem conj_of_mem_T₁t {t' : G} (ht' : t' * D.t⁻¹ ∈ D.T₁) :
    t' * D.b₀ * t'⁻¹ = D.b₁ ∧ t' * D.b₁ * t'⁻¹ = D.b₀ ∧
      ∀ {a₁ : G}, a₁ ∈ D.A → a₁ ≠ 1 → a₁ ≠ D.a → t' * a₁ * t'⁻¹ = D.a * a₁ := by
  set g := t' * D.t⁻¹ with hg_def
  have ht'eq : t' = g * D.t := by rw [hg_def]; group
  refine ⟨?_, ?_, ?_⟩
  · rw [ht'eq]
    calc g * D.t * D.b₀ * (g * D.t)⁻¹ = g * (D.t * D.b₀ * D.t⁻¹) * g⁻¹ := by group
      _ = D.b₁ := by rw [D.conj_t_b₀, D.b₁_comm_T₁ ht', mul_inv_cancel_right]
  · rw [ht'eq]
    calc g * D.t * D.b₁ * (g * D.t)⁻¹ = g * (D.t * D.b₁ * D.t⁻¹) * g⁻¹ := by group
      _ = D.b₀ := by rw [D.conj_t_b₁, D.b₀_comm_T₁ ht', mul_inv_cancel_right]
  · intro a₁ ha₁ ha₁1 ha₁a
    have hta : D.t * a₁ * D.t⁻¹ ∈ D.A := D.conj_t_A a₁ ha₁
    have hy : D.t * a₁ * D.t⁻¹ = D.a * a₁ := by
      rcases D.mem_A_of_two ha₁ ha₁1 ha₁a hta with h | h | h | h
      · exact absurd (conj_eq_one_iff.1 h) ha₁1
      · exfalso
        apply ha₁a
        have hta' : D.t * D.a = D.a * D.t := D.a_comm_T D.t_mem_T
        calc a₁ = D.t⁻¹ * (D.t * a₁ * D.t⁻¹) * D.t := by group
          _ = D.t⁻¹ * D.a * D.t := by rw [h]
          _ = D.a := by rw [mul_assoc, ← hta', ← mul_assoc, inv_mul_cancel, one_mul]
      · exfalso
        have hc : a₁ * D.t = D.t * a₁ := by
          calc a₁ * D.t = (D.t * a₁ * D.t⁻¹) * D.t := by rw [h]
            _ = D.t * a₁ := by group
        rcases D.eq_one_or_a_of_comm_t ha₁ hc with h' | h'
        · exact ha₁1 h'
        · exact ha₁a h'
      · exact h
    rw [ht'eq]
    calc g * D.t * a₁ * (g * D.t)⁻¹ = g * (D.t * a₁ * D.t⁻¹) * g⁻¹ := by group
      _ = D.a * a₁ := by rw [hy, D.A_comm_T₁ ht' (mul_mem D.a_mem ha₁), mul_inv_cancel_right]

end FooteCore

namespace FooteData

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteData G (T : Subgroup G) 2 n)

theorem lemma11_core (hL3 : ∀ y ∈ D.Zab, IsConj D.a y → y = D.a)
    {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F) [IsMulCommutative ↥F]
    {d₀ d₁ t' : G} (hd₀B₀ : d₀ ∈ D.B₀) (hd₀N : d₀ ∈ normalizer (F : Set G))
    (hd₁B₁ : d₁ ∈ D.B₁) (hd₁N : d₁ ∈ normalizer (F : Set G))
    (ht'T : t' ∈ (T : Subgroup G)) (ht'N : t' ∈ normalizer (F : Set G)) (ht'2 : t' * t' = 1)
    (ht'T₁ : t' * D.t⁻¹ ∈ D.T₁) {x₀ x₁ : NBar.Q F}
    (h : Normalizer.Lemma11Hyp (NBar.ρ F) (NBar.π F ⟨d₀, hd₀N⟩) (NBar.π F ⟨d₁, hd₁N⟩) x₀ x₁
      (NBar.π F ⟨t', ht'N⟩) ⟨D.b₀, D.b₀_mem_E64 hF⟩ ⟨D.b₁, D.b₁_mem_E64 hF⟩) :
    NBar.ρ F x₀ ⟨D.a, D.a_mem_E64 hF⟩ = ⟨D.a, D.a_mem_E64 hF⟩ := by
  classical
  by_contra hmove
  have hF2 := hF.mul_self
  have hFc : ∀ u ∈ F, ∀ v ∈ F, u * v = v * u := fun u hu v hv =>
    TStruct.comm_of_mul_self hF2 hu hv
  have haF : D.a ∈ F := D.a_mem_E64 hF
  have hb₀F : D.b₀ ∈ F := D.b₀_mem_E64 hF
  have hb₁F : D.b₁ ∈ F := D.b₁_mem_E64 hF
  have hAF : D.A ≤ F := D.A_le_E64 rfl hF
  have hval : ∀ (gN : ↥(normalizer (F : Set G))) (v : ↥F),
      ((NBar.ρ F (NBar.π F gN) v : ↥F) : G) = gN * v * (gN : G)⁻¹ := NBar.ρ_π F
  have hconjv : ∀ (gN : ↥(normalizer (F : Set G))) {v v' : ↥F}, NBar.ρ F (NBar.π F gN) v = v' →
      IsConj (v : G) (v' : G) := fun gN v v' hv =>
    isConj_iff.2 ⟨gN, by rw [← hval, hv]⟩
  have happG : ∀ (gN : ↥(normalizer (F : Set G))) {v v' : ↥F}, NBar.ρ F (NBar.π F gN) v = v' →
      (gN : G) * v * (gN : G)⁻¹ = v' := fun gN v v' hv => by rw [← hval, hv]
  have hconjX : ∀ (g : NBar.Q F) {v v' : ↥F}, NBar.ρ F g v = v' → IsConj (v : G) (v' : G) := by
    intro g v v' hv
    obtain ⟨gN, rfl⟩ := NBar.π_surjective F g
    exact hconjv gN hv
  have hT₁B : ∀ {β : G}, β ∈ D.B → β * D.a * β⁻¹ = D.a := fun hβ => by
    rw [← D.A_comm_B D.a D.a_mem _ hβ, mul_inv_cancel_right]
  have hAB : ∀ {x : G}, x ∈ D.A → x ∈ D.B → x = 1 := by
    intro x hxA hxB
    have : x ∈ D.A ⊓ D.B := mem_inf.2 ⟨hxA, hxB⟩
    rwa [D.A_inf_B, mem_bot] at this
  have hfactor : ∀ {α₁ α₂ β₁ β₂ : G}, α₁ ∈ D.A → α₂ ∈ D.A → β₁ ∈ D.B → β₂ ∈ D.B →
      α₁ * β₁ = α₂ * β₂ → α₁ = α₂ ∧ β₁ = β₂ := fun h1 h2 h3 h4 he =>
    TStruct.eq_and_eq_of_mul_eq_mul D.A_inf_B h1 h2 h3 h4 he
  have ht'0 : t' ∉ D.T₀ := by
    intro ht'
    apply D.t_not_mem_T₀
    have : D.t = (t' * D.t⁻¹)⁻¹ * t' := by group
    rw [this]
    exact mul_mem (inv_mem (D.T₁_le_T₀ ht'T₁)) ht'
  obtain ⟨ht'b₀, ht'b₁, ht'A⟩ := D.conj_of_mem_T₁t ht'T₁
  have ht'a : t' * D.a * t'⁻¹ = D.a := by rw [D.a_comm_T ht'T, mul_inv_cancel_right]
  set w : ↥F := ⟨D.a, haF⟩ with hw_def
  set c₀ : ↥F := ⟨D.b₀, hb₀F⟩ with hc₀_def
  set c₁ : ↥F := ⟨D.b₁, hb₁F⟩ with hc₁_def
  set d₀b := NBar.π F ⟨d₀, hd₀N⟩ with hd₀b_def
  set d₁b := NBar.π F ⟨d₁, hd₁N⟩ with hd₁b_def
  set τb := NBar.π F ⟨t', ht'N⟩ with hτb_def
  set U₀ := commV (zpowers (NBar.ρ F x₀)) with hU₀_def
  set U₁ := commV (zpowers (NBar.ρ F x₁)) with hU₁_def
  set A₁ := fixV (zpowers (NBar.ρ F x₀)) ⊓ fixV (zpowers (NBar.ρ F x₁)) with hA₁_def
  have hw1 : w ≠ 1 := fun h' => D.a_ne_one (congrArg Subtype.val h')
  have hc₀1 : c₀ ≠ 1 := fun h' => D.b₀_ne_one (congrArg Subtype.val h')
  have hc₁1 : c₁ ≠ 1 := fun h' => D.b₁_ne_one (congrArg Subtype.val h')
  have hd₀w : NBar.ρ F d₀b w = w := Subtype.ext (by rw [hval]; exact hT₁B (D.B₀_le_B hd₀B₀))
  have hd₁w : NBar.ρ F d₁b w = w := Subtype.ext (by rw [hval]; exact hT₁B (D.B₁_le_B hd₁B₁))
  have hτw : NBar.ρ F τb w = w := Subtype.ext (by rw [hval]; exact ht'a)
  have hOfix : ∀ g ∈ pPrimeCore 2 (NBar.Q F), ∀ v ∈ A₁, NBar.ρ F g v = v :=
    fun g hg v hv => (h.mem_fix_iff.1 hv) g hg
  have hx₀O : ∀ g ∈ zpowers x₀, g ∈ pPrimeCore 2 (NBar.Q F) := fun g hg => by
    rw [h.core_eq]
    exact mem_sup_left hg
  set e : ↥F := NBar.ρ F x₀ w with he_def
  have hconj_e : IsConj D.a (e : G) := hconjX x₀ (v := w) rfl
  have he_ne : e ≠ w := hmove
  set u : ↥F := e * w⁻¹ with hu_def
  have huU : u ∈ U₀ := subset_closure ⟨NBar.ρ F x₀, mem_zpowers _, w, rfl⟩
  have hu1 : u ≠ 1 := fun h' => he_ne (mul_inv_eq_one.1 h')
  have hDZ : ∀ {y : G}, y ∈ D.Zab → IsConj D.a y → y = D.a := fun hy hc => hL3 _ hy hc
  have haZ : D.a ∈ D.Zab := subset_closure (Set.mem_insert _ _)
  have hb₀Z : D.b₀ ∈ D.Zab := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb₁Z : D.b₁ ∈ D.Zab :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hub : u ≠ c₀ := by
    intro h'
    have he' : e = c₀ * w := by rw [← h', hu_def, inv_mul_cancel_right]
    have hev : (e : G) = D.b₀ * D.a := by rw [he']; rfl
    have := hDZ (y := (e : G)) (by rw [hev]; exact mul_mem hb₀Z haZ) hconj_e
    apply D.b₀_ne_one
    calc D.b₀ = D.b₀ * D.a * D.a⁻¹ := by group
      _ = 1 := by rw [← hev, this, mul_inv_cancel]
  obtain ⟨a₂, ha₂FA, r₀, hr₀FB, r₁, hr₁FB, he_eq⟩ := (D.mem_E64_iff hF).1 e.2
  have ha₂A : a₂ ∈ D.A := (mem_inf.1 ha₂FA).2
  have hr₀B₀ : r₀ ∈ D.B₀ := (mem_inf.1 hr₀FB).2
  have hr₁B₁ : r₁ ∈ D.B₁ := (mem_inf.1 hr₁FB).2
  have hr₀F : r₀ ∈ F := (mem_inf.1 hr₀FB).1
  have hd₁e : NBar.ρ F d₁b e = e := by
    show NBar.ρ F d₁b (NBar.ρ F x₀ w) = NBar.ρ F x₀ w
    rw [← MulAut.mul_apply, ← map_mul, h.comm₁₀, map_mul, MulAut.mul_apply, hd₁w]
  have hmove₁ : ∃ v ∈ F, d₁ * v * d₁⁻¹ ≠ v := by
    obtain ⟨v, hv⟩ := B1.exists_moved_of_ne_one h.ne_one₁
    exact ⟨v, v.2, fun h' => hv (Subtype.ext (by rw [hval]; exact h'))⟩
  have hr₁' : r₁ = 1 ∨ r₁ = D.b₁ := by
    have hfix : d₁ * (e : G) * d₁⁻¹ = e := happG ⟨d₁, hd₁N⟩ hd₁e
    rw [he_eq, D.conj_decomp_B₁ hd₁B₁ ha₂A hr₀B₀] at hfix
    exact D.eq_one_or_b₁_of_fix_E64 hF hd₁B₁ hmove₁ hr₁FB
      (mul_left_cancel (mul_left_cancel hfix))
  have hu_val : (u : G) = (D.a * a₂) * (r₀ * r₁) := by
    show (e : G) * D.a⁻¹ = _
    rw [he_eq, inv_eq_of_mul_eq_one_right D.a_mul_a]
    have hc : (a₂ * (r₀ * r₁)) * D.a = D.a * (a₂ * (r₀ * r₁)) :=
      D.a_comm_T (mul_mem (D.A_le_T ha₂A) (mul_mem (D.B_le_T (D.B₀_le_B hr₀B₀))
        (D.B_le_T (D.B₁_le_B hr₁B₁))))
    rw [hc]
    group
  have hd₀u := h.d₀_apply huU hu1 hub
  have hr₀d : d₀ * r₀ * d₀⁻¹ = r₀ * D.b₀ := by
    have h1 : d₀ * (u : G) * d₀⁻¹ = (u : G) * D.b₀ := happG ⟨d₀, hd₀N⟩ hd₀u
    rw [hu_val, D.conj_decomp_B₀ hd₀B₀ (mul_mem D.a_mem ha₂A) hr₁B₁] at h1
    have hcomm : r₁ * D.b₀ = D.b₀ * r₁ := (D.B₀_comm_B₁ D.b₀ D.b₀_mem r₁ hr₁B₁).symm
    have h2 : (d₀ * r₀ * d₀⁻¹) * r₁ = (r₀ * D.b₀) * r₁ := by
      have h3 := mul_left_cancel (h1.trans (mul_assoc _ _ _))
      rw [h3, mul_assoc, hcomm, ← mul_assoc]
    exact mul_right_cancel h2
  have hr₀1 : r₀ ≠ 1 := by
    intro h'
    rw [h', mul_one, mul_inv_cancel, one_mul] at hr₀d
    exact D.b₀_ne_one hr₀d.symm
  have hr₀b : r₀ ≠ D.b₀ := by
    intro h'
    rw [h', D.b₀_comm d₀ hd₀B₀, mul_inv_cancel_right, D.b₀_mul_b₀] at hr₀d
    exact D.b₀_ne_one hr₀d
  have hr₀2 : orderOf r₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hF2 r₀ hr₀F) hr₀1
  have hV : ∀ v : ↥F, v * v = 1 := fun v => Subtype.ext (hF2 v v.2)
  have hinv : ∀ v : ↥F, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hV v)
  have hc₀U₀ : c₀ ∈ U₀ := h.comm₀_facts.2.1
  have hc₁U₁ : c₁ ∈ U₁ := h.comm₁_facts.2.1
  have hU₀U₁ : U₀ ⊓ U₁ = ⊥ := h.comm_inf_comm
  have hsup : A₁ ⊔ U₀ ⊔ U₁ = ⊤ := h.fix_sup_eq
  have hA₁B : A₁ ⊓ closure ({c₀, c₁} : Set ↥F) = ⊥ := h.fix_inf_closure_eq
  have hd₀A₁ : ∀ v ∈ A₁, NBar.ρ F d₀b v = v := h.d₀_fix
  have hd₁A₁ : ∀ v ∈ A₁, NBar.ρ F d₁b v = v := h.d₁_fix
  have hτA₁ : ∀ v ∈ A₁, NBar.ρ F τb v ∈ A₁ := h.fix_invariant τb
  have hd₀U₁ : ∀ v ∈ U₁, NBar.ρ F d₀b v = v := by
    intro v hv
    have hmem : NBar.ρ F d₀b v ∈ U₁ := commV_zpowers_invariant (by
      rw [← map_mul, ← map_mul, h.comm₀₁]) hv
    rcases h.tv₀.2 v with h1 | h1
    · exact h1
    · exfalso
      apply hc₀1
      have hc : c₀ ∈ U₀ ⊓ U₁ := by
        refine mem_inf.2 ⟨hc₀U₀, ?_⟩
        have : c₀ = v⁻¹ * NBar.ρ F d₀b v := by rw [h1]; group
        rw [this]
        exact mul_mem (inv_mem hv) hmem
      rwa [hU₀U₁, mem_bot] at hc
  have hd₁U₀ : ∀ v ∈ U₀, NBar.ρ F d₁b v = v := by
    intro v hv
    have hmem : NBar.ρ F d₁b v ∈ U₀ := commV_zpowers_invariant (by
      rw [← map_mul, ← map_mul, h.comm₁₀]) hv
    rcases h.tv₁.2 v with h1 | h1
    · exact h1
    · exfalso
      apply hc₁1
      have hc : c₁ ∈ U₀ ⊓ U₁ := by
        refine mem_inf.2 ⟨?_, hc₁U₁⟩
        have : c₁ = v⁻¹ * NBar.ρ F d₁b v := by rw [h1]; group
        rw [this]
        exact mul_mem (inv_mem hv) hmem
      rwa [hU₀U₁, mem_bot] at hc
  have hU₀fix : ∀ v ∈ U₀, NBar.ρ F d₀b v = v → v = 1 ∨ v = c₀ := by
    intro v hv hfix
    by_contra hcon
    push Not at hcon
    have := h.d₀_apply hv hcon.1 hcon.2
    rw [hfix] at this
    exact hc₀1 (mul_left_cancel (this.symm.trans (mul_one v).symm))
  have hU₁fix : ∀ v ∈ U₁, NBar.ρ F d₁b v = v → v = 1 ∨ v = c₁ := by
    intro v hv hfix
    by_contra hcon
    push Not at hcon
    have := h.d₁_apply hv hcon.1 hcon.2
    rw [hfix] at this
    exact hc₁1 (mul_left_cancel (this.symm.trans (mul_one v).symm))
  have hdec : ∀ y : ↥F, NBar.ρ F d₀b y = y → NBar.ρ F d₁b y = y →
      ∃ v ∈ A₁, ∃ β₀ β₁ : ↥F, (β₀ = 1 ∨ β₀ = c₀) ∧ (β₁ = 1 ∨ β₁ = c₁) ∧ y = v * (β₀ * β₁) := by
    intro y hy₀ hy₁
    have hy : y ∈ A₁ ⊔ U₀ ⊔ U₁ := hsup ▸ mem_top y
    obtain ⟨y', hy', u₁, hu₁, rfl⟩ := mem_sup.1 hy
    obtain ⟨v, hv, u₀, hu₀, rfl⟩ := mem_sup.1 hy'
    have hu₀f : NBar.ρ F d₀b u₀ = u₀ := by
      rw [map_mul, map_mul, hd₀A₁ v hv, hd₀U₁ u₁ hu₁] at hy₀
      exact mul_left_cancel (mul_right_cancel hy₀)
    have hu₁f : NBar.ρ F d₁b u₁ = u₁ := by
      rw [map_mul, map_mul, hd₁A₁ v hv, hd₁U₀ u₀ hu₀] at hy₁
      exact mul_left_cancel hy₁
    exact ⟨v, hv, u₀, u₁, hU₀fix u₀ hu₀ hu₀f, hU₁fix u₁ hu₁ hu₁f, by rw [mul_assoc]⟩
  have hτc₀ : NBar.ρ F τb c₀ = c₁ := Subtype.ext (by rw [hval]; exact ht'b₀)
  have hτc₁ : NBar.ρ F τb c₁ = c₀ := Subtype.ext (by rw [hval]; exact ht'b₁)
  have hc₀c₁ : c₀ ≠ c₁ := fun h' => D.b₀_ne_b₁ (congrArg Subtype.val h')
  have hmemB : ∀ {β₀ β₁ : ↥F}, (β₀ = 1 ∨ β₀ = c₀) → (β₁ = 1 ∨ β₁ = c₁) →
      β₀ * β₁ ∈ closure ({c₀, c₁} : Set ↥F) := by
    intro β₀ β₁ h0 h1
    refine mul_mem ?_ ?_
    · rcases h0 with rfl | rfl
      · exact one_mem _
      · exact subset_closure (Set.mem_insert _ _)
    · rcases h1 with rfl | rfl
      · exact one_mem _
      · exact subset_closure (Set.mem_insert_of_mem _ rfl)
  have hτmemB : ∀ {β₀ β₁ : ↥F}, (β₀ = 1 ∨ β₀ = c₀) → (β₁ = 1 ∨ β₁ = c₁) →
      NBar.ρ F τb (β₀ * β₁) ∈ closure ({c₀, c₁} : Set ↥F) := by
    intro β₀ β₁ h0 h1
    rw [map_mul]
    refine mul_mem ?_ ?_
    · rcases h0 with rfl | rfl
      · rw [map_one]; exact one_mem _
      · rw [hτc₀]; exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · rcases h1 with rfl | rfl
      · rw [map_one]; exact one_mem _
      · rw [hτc₁]; exact subset_closure (Set.mem_insert _ _)
  have hA₁B1 : ∀ {x : ↥F}, x ∈ A₁ → x ∈ closure ({c₀, c₁} : Set ↥F) → x = 1 := by
    intro x h1 h2
    have : x ∈ A₁ ⊓ closure ({c₀, c₁} : Set ↥F) := mem_inf.2 ⟨h1, h2⟩
    rwa [hA₁B, mem_bot] at this
  obtain ⟨v, hvA₁, β₀, β₁, hβ₀, hβ₁, hwv⟩ := hdec w hd₀w hd₁w
  have hβ : β₀ = c₀ ∧ β₁ = c₁ := by
    have hvw : v = w * (β₀ * β₁)⁻¹ := by rw [hwv]; group
    have hτv : NBar.ρ F τb v = w * (NBar.ρ F τb (β₀ * β₁))⁻¹ := by
      rw [hvw, map_mul, map_inv, hτw]
    have hfixβ : NBar.ρ F τb (β₀ * β₁) = β₀ * β₁ := by
      have hm : v⁻¹ * NBar.ρ F τb v ∈ A₁ := mul_mem (inv_mem hvA₁) (hτA₁ v hvA₁)
      have he : v⁻¹ * NBar.ρ F τb v = (β₀ * β₁) * (NBar.ρ F τb (β₀ * β₁))⁻¹ := by
        rw [hτv, hvw]; group
      rw [he] at hm
      have h1 := hA₁B1 hm (mul_mem (hmemB hβ₀ hβ₁) (inv_mem (hτmemB hβ₀ hβ₁)))
      exact (mul_inv_eq_one.1 h1).symm
    rcases hβ₀ with rfl | rfl <;> rcases hβ₁ with rfl | rfl
    · exfalso
      apply hmove
      have hv' : v = w := by rw [hvw]; group
      have hfx : NBar.ρ F x₀ v = v := (mem_inf.1 hvA₁).1 _ (mem_zpowers _)
      rw [hv'] at hfx
      exact hfx
    · exfalso
      rw [one_mul, hτc₁] at hfixβ
      exact hc₀c₁ hfixβ
    · exfalso
      rw [mul_one, hτc₀] at hfixβ
      exact hc₀c₁ hfixβ.symm
    · exact ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hβ
  have hab : w * (c₀ * c₁)⁻¹ ∈ A₁ := by
    have : v = w * (c₀ * c₁)⁻¹ := by rw [hwv]; group
    rw [← this]; exact hvA₁
  obtain ⟨a₁', ha₁'A, ha₁'Z⟩ : ∃ x ∈ D.A, x ∉ zpowers D.a := by
    by_contra hcon
    push Not at hcon
    haveI := D.finite_A
    have hle := Subgroup.card_le_of_le (show D.A ≤ zpowers D.a from hcon)
    rw [D.card_A, Nat.card_zpowers, D.a_order] at hle
    norm_num at hle
  have ha₁'1 : a₁' ≠ 1 := fun h' => ha₁'Z (h' ▸ one_mem _)
  have ha₁'a : a₁' ≠ D.a := fun h' => ha₁'Z (h' ▸ mem_zpowers _)
  have hya : ∃ ya : ↥F, (ya : G) ∈ D.A ∧ (ya : G) ≠ 1 ∧ (ya : G) ≠ D.a ∧ ya * c₀ ∈ A₁ := by
    set ya : ↥F := ⟨a₁', hAF ha₁'A⟩ with hya_def
    have hAcomm : ∀ {β x : G}, β ∈ D.B → x ∈ D.A → β * x * β⁻¹ = x := fun hβ hx => by
      rw [← D.A_comm_B _ hx _ hβ, mul_inv_cancel_right]
    have hd₀y : NBar.ρ F d₀b ya = ya :=
      Subtype.ext (by rw [hval]; exact hAcomm (D.B₀_le_B hd₀B₀) ha₁'A)
    have hd₁y : NBar.ρ F d₁b ya = ya :=
      Subtype.ext (by rw [hval]; exact hAcomm (D.B₁_le_B hd₁B₁) ha₁'A)
    have hτy : NBar.ρ F τb ya = w * ya :=
      Subtype.ext (by rw [hval]; exact ht'A ha₁'A ha₁'1 ha₁'a)
    obtain ⟨v₁, hv₁A₁, γ₀, γ₁, hγ₀, hγ₁, hyv⟩ := hdec ya hd₀y hd₁y
    have hv₁eq : v₁ = ya * (γ₀ * γ₁)⁻¹ := by rw [hyv]; group
    have hbad : NBar.ρ F τb (γ₀ * γ₁) = γ₀ * γ₁ → False := by
      intro hfix
      have hτv₁ : NBar.ρ F τb v₁ = (w * ya) * (γ₀ * γ₁)⁻¹ := by
        rw [hv₁eq, map_mul, map_inv, hτy, hfix]
      have hvv : v₁⁻¹ * NBar.ρ F τb v₁ = w := by
        rw [hτv₁, hv₁eq, mul_comm w ya]
        calc (ya * (γ₀ * γ₁)⁻¹)⁻¹ * (ya * w * (γ₀ * γ₁)⁻¹) = (γ₀ * γ₁) * w * (γ₀ * γ₁)⁻¹ := by
              group
          _ = w := by rw [mul_comm (γ₀ * γ₁) w, mul_inv_cancel_right]
      have hm : (w * (c₀ * c₁)⁻¹)⁻¹ * w ∈ A₁ :=
        mul_mem (inv_mem hab) (hvv ▸ mul_mem (inv_mem hv₁A₁) (hτA₁ v₁ hv₁A₁))
      have he : (w * (c₀ * c₁)⁻¹)⁻¹ * w = c₀ * c₁ := by group
      rw [he] at hm
      have h1 := hA₁B1 hm (hmemB (Or.inr rfl) (Or.inr rfl))
      apply hc₀c₁
      calc c₀ = c₀ * (c₁ * c₁) := by rw [hV, mul_one]
        _ = c₁ := by rw [← mul_assoc, h1, one_mul]
    rcases hγ₀ with rfl | rfl <;> rcases hγ₁ with rfl | rfl
    · exact (hbad (by rw [one_mul, map_one])).elim
    ·
      refine ⟨w * ya, mul_mem D.a_mem ha₁'A, ?_, ?_, ?_⟩
      · intro h'
        apply ha₁'a
        have : (w : G) * ya = 1 := h'
        calc a₁' = D.a⁻¹ * ((w : G) * ya) := by
              show a₁' = D.a⁻¹ * (D.a * a₁')
              group
          _ = D.a := by rw [this, mul_one, inv_eq_of_mul_eq_one_right D.a_mul_a]
      · intro h'
        apply ha₁'1
        have : (w : G) * ya = D.a := h'
        calc a₁' = D.a⁻¹ * ((w : G) * ya) := by
              show a₁' = D.a⁻¹ * (D.a * a₁')
              group
          _ = 1 := by rw [this, inv_mul_cancel]
      · have hv₁' : v₁ = ya * c₁ := by rw [hv₁eq, one_mul, hinv]
        have hm := mul_mem hab (hv₁' ▸ hv₁A₁)
        have he : w * (c₀ * c₁)⁻¹ * (ya * c₁) = w * ya * c₀ := by
          rw [mul_inv_rev, hinv, hinv, mul_mul_mul_comm]
          congr 1
          rw [mul_assoc, mul_comm c₀ c₁, ← mul_assoc, hV, one_mul]
        rwa [he] at hm
    · refine ⟨ya, ha₁'A, ha₁'1, ha₁'a, ?_⟩
      have hv₁' : v₁ = ya * c₀ := by rw [hv₁eq, mul_one, hinv]
      exact hv₁' ▸ hv₁A₁
    · exact (hbad (by rw [map_mul, hτc₀, hτc₁, mul_comm])).elim
  obtain ⟨ya, hyaA, hya1, hyaa, hyaA₁⟩ := hya
  have hVV : ∀ v y : ↥F, v * (v * y) = y := fun v y => by rw [← mul_assoc, hV, one_mul]
  have hinvol : ∀ {x : G}, x ∈ D.A → x ≠ 1 → orderOf x = 2 := fun hx hx1 =>
    orderOf_eq_prime (by rw [sq]; exact D.mul_self_of_two hx) hx1
  set a₂F : ↥F := ⟨a₂, (mem_inf.1 ha₂FA).1⟩ with ha₂F_def
  set r₀F : ↥F := ⟨r₀, hr₀F⟩ with hr₀F_def
  set r₁F : ↥F := ⟨r₁, (mem_inf.1 hr₁FB).1⟩ with hr₁F_def
  have hu_F : u = (w * a₂F) * (r₀F * r₁F) := Subtype.ext hu_val
  have he_F : e = a₂F * (r₀F * r₁F) := Subtype.ext he_eq
  have hyaA' : D.a * (ya : G) ∈ D.A := mul_mem D.a_mem hyaA
  have hwya1 : D.a * (ya : G) ≠ 1 := by
    intro h'; apply hyaa
    calc (ya : G) = D.a * (D.a * ya) := by rw [← mul_assoc, D.a_mul_a, one_mul]
      _ = D.a := by rw [h', mul_one]
  have hwyaa : D.a * (ya : G) ≠ D.a := by
    intro h'; apply hya1
    calc (ya : G) = D.a * (D.a * ya) := by rw [← mul_assoc, D.a_mul_a, one_mul]
      _ = 1 := by rw [h', D.a_mul_a]
  have ha₂' := D.mem_A_of_two hyaA hya1 hyaa ha₂A
  have hz₁ : ∀ g ∈ pPrimeCore 2 (NBar.Q F), NBar.ρ F g (w * (c₀ * c₁)⁻¹) = w * (c₀ * c₁)⁻¹ :=
    fun g hg => hOfix g hg _ hab
  have hz₂ : ∀ g ∈ pPrimeCore 2 (NBar.Q F), NBar.ρ F g (ya * c₀) = ya * c₀ :=
    fun g hg => hOfix g hg _ hyaA₁
  rcases hr₁' with hr₁1 | hr₁b
  ·
    have hr₁F : r₁F = 1 := Subtype.ext hr₁1
    have ha₂Z : a₂ = 1 ∨ a₂ = D.a := by
      rcases ha₂' with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exfalso
        apply D.fusion_i a₂ ha₂A (hinvol ha₂A (by rw [h']; exact hya1)) (by rw [h']; exact hyaa)
          r₀ hr₀B₀ hr₀2
        have := hconj_e
        rwa [he_eq, hr₁1, mul_one] at this
      · exfalso
        apply D.fusion_i a₂ ha₂A (hinvol ha₂A (by rw [h']; exact hwya1)) (by rw [h']; exact hwyaa)
          r₀ hr₀B₀ hr₀2
        have := hconj_e
        rwa [he_eq, hr₁1, mul_one] at this
    have huc : u * c₀ ∈ U₀ := mul_mem huU hc₀U₀
    have huc1 : u * c₀ ≠ 1 := by
      intro h'
      have hv : (D.a * a₂) * (r₀ * D.b₀) = 1 * 1 := by
        have := congrArg Subtype.val h'
        rw [Subgroup.coe_mul, hu_val, hr₁1, mul_one] at this
        rw [← mul_assoc, this, mul_one]
        rfl
      have := (hfactor (mul_mem D.a_mem ha₂A) (one_mem _)
        (mul_mem (D.B₀_le_B hr₀B₀) D.b₀_mem_B) (one_mem _) hv).2
      apply hr₀b
      calc r₀ = r₀ * D.b₀ * D.b₀ := by rw [mul_assoc, D.b₀_mul_b₀, mul_one]
        _ = D.b₀ := by rw [this, one_mul]
    obtain ⟨g, hg, hgc⟩ := h.exists_conj₀ huc huc1
    have hgya : NBar.ρ F g ya = ya * u := by
      have h1 := hz₂ g (hx₀O g hg)
      rw [map_mul, hgc] at h1
      calc NBar.ρ F g ya = NBar.ρ F g ya * (u * c₀) * (u * c₀)⁻¹ := by group
        _ = ya * c₀ * (u * c₀)⁻¹ := by rw [h1]
        _ = ya * u := by
            rw [mul_inv_rev, hinv u, hinv c₀, ← mul_assoc, mul_assoc ya c₀ c₀, hV, mul_one]
    have hconj := hconjX g hgya
    have hval' : ((ya * u : ↥F) : G) = ((ya : G) * (D.a * a₂)) * r₀ := by
      rw [Subgroup.coe_mul, hu_val, hr₁1, mul_one]
      simp only [mul_assoc]
    rw [hval'] at hconj
    have hx : (ya : G) * (D.a * a₂) ∈ D.A := mul_mem hyaA (mul_mem D.a_mem ha₂A)
    have hx1 : (ya : G) * (D.a * a₂) ≠ 1 ∧ (ya : G) * (D.a * a₂) ≠ D.a := by
      rcases ha₂Z with h' | h'
      · rw [h', mul_one, D.A_comm_of_two hyaA D.a_mem]
        exact ⟨hwya1, hwyaa⟩
      · rw [h', D.a_mul_a, mul_one]
        exact ⟨hya1, hyaa⟩
    exact D.fusion_iii _ hx (hinvol hx hx1.1) hx1.2 _ hyaA (hinvol hyaA hya1) hyaa r₀ hr₀B₀ hr₀2
      hconj.symm
  ·
    have hr₁F : r₁F = c₁ := Subtype.ext hr₁b
    rcases ha₂' with ha₂1 | ha₂a | ha₂y | ha₂y
    ·
      apply D.fusion_ii r₀ hr₀B₀ hr₀2
      have := hconj_e
      rwa [he_eq, hr₁b, ha₂1, one_mul] at this
    ·
      have hu' : u = r₀F * c₁ := by
        rw [hu_F, hr₁F]
        have : w * a₂F = 1 := Subtype.ext (by
          show D.a * a₂ = 1
          rw [ha₂a, D.a_mul_a])
        rw [this, one_mul]
      obtain ⟨g, hg, hgc⟩ := h.exists_conj_mul huU hu1 hc₁U₁ hc₁1
      have h1 : NBar.ρ F g (w * (c₀ * c₁)⁻¹ * (ya * c₀) * (c₀ * c₁)) =
          w * (c₀ * c₁)⁻¹ * (ya * c₀) * (u * c₁) := by
        rw [map_mul, map_mul, hz₁ g hg, hz₂ g hg, hgc]
      have e1 : w * (c₀ * c₁)⁻¹ * (ya * c₀) * (c₀ * c₁) = w * ya * c₀ := by
        simp only [mul_inv_rev, hinv, mul_assoc, mul_comm, mul_left_comm, hV, hVV, mul_one,
          one_mul]
      have e2 : w * (c₀ * c₁)⁻¹ * (ya * c₀) * (u * c₁) = w * ya * (r₀F * c₁) := by
        rw [hu']
        simp only [mul_inv_rev, hinv, mul_assoc, mul_comm, mul_left_comm, hV, hVV, mul_one,
          one_mul]
      rw [e1, e2] at h1
      have hconj := hconjX g h1
      have hv1 : ((w * ya * c₀ : ↥F) : G) = (D.a * ya) * D.b₀ := rfl
      have hv2 : ((w * ya * (r₀F * c₁) : ↥F) : G) = (D.a * ya) * r₀ * D.b₁ := by
        show D.a * ya * (r₀ * D.b₁) = _
        simp only [mul_assoc]
      rw [hv1, hv2] at hconj
      exact D.fusion_iv _ hyaA' (hinvol hyaA' hwya1) hwyaa r₀ hr₀B₀ hr₀2 hconj.symm
    all_goals
      have hτya : NBar.ρ F τb ya = w * ya :=
        Subtype.ext (by rw [hval]; exact ht'A hyaA hya1 hyaa)
      have hcase : ∀ αF : ↥F, u = αF * (r₀F * c₁) → NBar.ρ F τb αF = w * αF → False := by
        intro αF huα hτα
        set r₀F' := NBar.ρ F τb r₀F with hr₀F'_def
        have hu'eq : NBar.ρ F τb u = (w * αF) * (r₀F' * c₀) := by
          rw [huα, map_mul, map_mul, hτα, hτc₁]
        have hu'U : NBar.ρ F τb u ∈ U₁ := by
          have hmap : U₀.map (NBar.ρ F τb).toMonoidHom = U₁ := h.map_comm_eq
          rw [← hmap]
          exact ⟨u, huU, rfl⟩
        have hu'1 : NBar.ρ F τb u ≠ 1 := fun h' =>
          hu1 ((NBar.ρ F τb).injective (h'.trans (map_one _).symm))
        obtain ⟨g, hg, hgc⟩ := h.exists_conj_mul huU hu1 hu'U hu'1
        have h1 : NBar.ρ F g w = w * (c₀ * c₁)⁻¹ * (u * NBar.ρ F τb u) := by
          have : w = w * (c₀ * c₁)⁻¹ * (c₀ * c₁) := by group
          conv_lhs => rw [this]
          rw [map_mul, hz₁ g hg, hgc]
        have e1 : w * (c₀ * c₁)⁻¹ * (u * NBar.ρ F τb u) = r₀F * r₀F' := by
          rw [hu'eq, huα, mul_inv_rev, hinv, hinv]
          calc w * (c₁ * c₀) * (αF * (r₀F * c₁) * (w * αF * (r₀F' * c₀)))
              = (w * w) * (αF * αF) * (c₁ * c₁) * (c₀ * c₀) * (r₀F * r₀F') := by ac_rfl
            _ = r₀F * r₀F' := by simp only [hV, one_mul]
        rw [e1] at h1
        have hconj := hconjX g h1
        have hv : ((r₀F * r₀F' : ↥F) : G) = r₀ * (t' * r₀ * t'⁻¹) := by
          show r₀ * ((NBar.ρ F τb r₀F : ↥F) : G) = _
          rw [hval]
        rw [hv] at hconj
        exact D.fusion_v_of_mem ht'T ht'0 ht'2 (Or.inl hr₀B₀) hr₀2 hconj
      first
        | exact hcase (w * ya) (by rw [hu_F, hr₁F, show a₂F = ya from Subtype.ext ha₂y])
            (by rw [map_mul, hτw, hτya])
        | exact hcase ya (by rw [hu_F, hr₁F, show a₂F = w * ya from Subtype.ext ha₂y, hVV]) hτya

end FooteData

end CFSG.CGT.Foote81L6
