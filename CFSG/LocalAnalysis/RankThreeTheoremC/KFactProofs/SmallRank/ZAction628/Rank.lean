module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.ElemModule
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Halving
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

section powHom

theorem powHom_pow_mul {x y c : K} (hc : c = y * x * y⁻¹ * x⁻¹) (hcy : Commute c y) (n : ℕ) :
    y ^ n * x = c ^ n * x * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hyx : y * x = c * x * y := by rw [hc]; group
    calc y ^ (n + 1) * x = y ^ n * (y * x) := by rw [pow_succ, mul_assoc]
      _ = y ^ n * (c * x * y) := by rw [hyx]
      _ = (y ^ n * c) * x * y := by simp only [mul_assoc]
      _ = (c * y ^ n) * x * y := by rw [← (hcy.pow_right n).eq]
      _ = c * (y ^ n * x) * y := by simp only [mul_assoc]
      _ = c * (c ^ n * x * y ^ n) * y := by rw [ih]
      _ = c ^ (n + 1) * x * y ^ (n + 1) := by
        rw [pow_succ' c n, pow_succ y n]
        simp only [mul_assoc]

theorem powHom_mul_pow {x y c : K} (hc : c = y * x * y⁻¹ * x⁻¹) (hcx : Commute c x)
    (hcy : Commute c y) (n : ℕ) : (x * y) ^ n = c ^ (n.choose 2) * x ^ n * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := powHom_pow_mul hc hcy n
    have hch : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = c ^ n.choose 2 * x ^ n * y ^ n * (x * y) := by rw [ih]
      _ = c ^ n.choose 2 * x ^ n * (y ^ n * x) * y := by simp only [mul_assoc]
      _ = c ^ n.choose 2 * x ^ n * (c ^ n * x * y ^ n) * y := by rw [h1]
      _ = c ^ n.choose 2 * (x ^ n * c ^ n) * x * y ^ n * y := by simp only [mul_assoc]
      _ = c ^ n.choose 2 * (c ^ n * x ^ n) * x * y ^ n * y := by
        rw [← (hcx.pow_pow n n).eq]
      _ = c ^ (n + 1).choose 2 * x ^ (n + 1) * y ^ (n + 1) := by
        rw [hch, pow_add, pow_succ x n, pow_succ y n]
        simp only [mul_assoc]

end powHom

theorem pow_mul_of_central {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) {P : Subgroup K}
    (hP' : ∀ x ∈ P, ∀ y ∈ P, ∀ w ∈ P, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    (hPf : ∀ x ∈ P, ∀ w ∈ P, w * x ^ f = x ^ f * w) {x y : K} (hx : x ∈ P) (hy : y ∈ P) :
    (x * y) ^ f = x ^ f * y ^ f := by
  have hc : ⁅y, x⁆ = y * x * y⁻¹ * x⁻¹ := commutatorElement_def y x
  have hcx : Commute ⁅y, x⁆ x := (hP' y hy x hx x hx).symm
  have hcy : Commute ⁅y, x⁆ y := (hP' y hy x hx y hy).symm
  have h1 := powHom_pow_mul hc hcy f
  have h2 := powHom_mul_pow hc hcx hcy f
  have hcf : ⁅y, x⁆ ^ f = 1 := by
    have hyf : x * y ^ f = y ^ f * x := hPf y hy x hx
    have h3 : ⁅y, x⁆ ^ f * x * y ^ f = 1 * x * y ^ f := by
      rw [← h1, one_mul, hyf]
    exact mul_right_cancel (mul_right_cancel h3)
  have hdvd : f ∣ f.choose 2 :=
    hf.dvd_choose_self (by norm_num) (by have := hf.two_le; omega)
  obtain ⟨k, hk⟩ := hdvd
  rw [h2, hk, pow_mul, hcf, one_pow, one_mul]
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

section orderFive

variable {G : Type} [Group G] [Finite G]

theorem orderFive_index_centralizer_le (hcl : ∀ x y w : G, w * ⁅x, y⁆ = ⁅x, y⁆ * w) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).index ≤ Nat.card (Subgroup.center G) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : G →* Subgroup.center G, ∀ y, (φ y : G) = ⁅y, x⁆ := by
    refine ⟨{ toFun := fun y => ⟨⁅y, x⁆, Subgroup.mem_center_iff.mpr fun g => hcl y x g⟩
              map_one' := ?_
              map_mul' := ?_ }, fun _ => rfl⟩
    · exact Subtype.ext (by simp)
    · intro a b
      apply Subtype.ext
      show ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆
      have e1 : b * x * b⁻¹ = ⁅b, x⁆ * x := by simp [commutatorElement_def, mul_assoc]
      calc ⁅a * b, x⁆ = a * (b * x * b⁻¹) * a⁻¹ * x⁻¹ := by
            simp [commutatorElement_def, mul_assoc]
        _ = a * (⁅b, x⁆ * x) * a⁻¹ * x⁻¹ := by rw [e1]
        _ = (a * ⁅b, x⁆) * x * a⁻¹ * x⁻¹ := by simp only [mul_assoc]
        _ = (⁅b, x⁆ * a) * x * a⁻¹ * x⁻¹ := by rw [hcl b x a]
        _ = ⁅b, x⁆ * ⁅a, x⁆ := by simp [commutatorElement_def, mul_assoc]
        _ = ⁅a, x⁆ * ⁅b, x⁆ := hcl a x ⁅b, x⁆
  have hker : φ.ker = Subgroup.centralizer ({x} : Set G) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      have h2 : ⁅y, u⁆ = 1 := by
        have := congrArg Subtype.val h
        simpa [hφ] using this
      exact ((commutatorElement_eq_one_iff_mul_comm).mp h2).symm
    · intro h
      apply Subtype.ext
      rw [hφ]
      exact (commutatorElement_eq_one_iff_mul_comm).mpr (h x rfl).symm
  rw [← hker, Subgroup.index_ker]
  exact Subgroup.card_le_card_group _

theorem orderFive_index_sup_le (hcl : ∀ x y w : G, w * ⁅x, y⁆ = ⁅x, y⁆ * w) (B : Subgroup G)
    (x : G) :
    (Subgroup.centralizer ((B ⊔ Subgroup.zpowers x : Subgroup G) : Set G)).index ≤
      (Subgroup.centralizer (B : Set G)).index * Nat.card (Subgroup.center G) := by
  have h1 : Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ((B ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyB, hyx⟩ := hy
    rw [Subgroup.mem_centralizer_iff] at hyB hyx ⊢
    intro h hh
    have hB : B ≤ Subgroup.centralizer ({y} : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (hyB b hb).symm
    have hx : Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (hyx x rfl).symm
    have := sup_le hB hx hh
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this y rfl).symm
  calc (Subgroup.centralizer ((B ⊔ Subgroup.zpowers x : Subgroup G) : Set G)).index
      ≤ (Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer ({x} : Set G)).index :=
        Subgroup.index_antitone h1
    _ ≤ (Subgroup.centralizer (B : Set G)).index *
          (Subgroup.centralizer ({x} : Set G)).index := Subgroup.index_inf_le
    _ ≤ (Subgroup.centralizer (B : Set G)).index * Nat.card (Subgroup.center G) :=
        Nat.mul_le_mul_left _ (orderFive_index_centralizer_le hcl x)

theorem orderFive_sup_abelian {B : Subgroup G} (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : ∀ b ∈ B, b * x = x * b) :
    ∀ a ∈ B ⊔ Subgroup.zpowers x, ∀ b ∈ B ⊔ Subgroup.zpowers x, a * b = b * a := by
  have step1 : ∀ a ∈ B, ∀ b ∈ B ⊔ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    have h1 : B ≤ Subgroup.centralizer ({a} : Set G) := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact hB u ha c hc
    have h2 : Subgroup.zpowers x ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (hx u ha)
    have := sup_le h1 h2 hb
    rw [Subgroup.mem_centralizer_iff] at this
    exact this a rfl
  have step2 : ∀ b ∈ B ⊔ Subgroup.zpowers x, x * b = b * x := by
    intro b hb
    have h1 : B ≤ Subgroup.centralizer ({x} : Set G) := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (hx c hc).symm
    have h2 : Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      rfl
    have := sup_le h1 h2 hb
    rw [Subgroup.mem_centralizer_iff] at this
    exact this x rfl
  intro a ha b hb
  have h1 : B ≤ Subgroup.centralizer ({b} : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact (step1 c hc u hb).symm
  have h2 : Subgroup.zpowers x ≤ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact (step2 u hb).symm
  have := sup_le h1 h2 ha
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this b rfl).symm

theorem orderFive_card_sup {f : ℕ} (hf : f.Prime) {B : Subgroup G} {x : G} (hx : x ^ f = 1)
    (hxB : x ∉ B) : f * Nat.card B ≤ Nat.card (B ⊔ Subgroup.zpowers x : Subgroup G) := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hx1 : x ≠ 1 := fun h => hxB (h ▸ B.one_mem)
  have hord : orderOf x = f := orderOf_eq_prime hx hx1
  have hcard : Nat.card (Subgroup.zpowers x) = f := by rw [Nat.card_zpowers, hord]
  have hdisj : Subgroup.zpowers x ⊓ B = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ B : Subgroup G) ∣ f := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hf).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : Subgroup.zpowers x ⊓ B = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard])
      have : x ∈ Subgroup.zpowers x ⊓ B := by
        rw [heq]; exact Subgroup.mem_zpowers x
      exact hxB this.2
  let g : Subgroup.zpowers x × B → (B ⊔ Subgroup.zpowers x : Subgroup G) := fun p =>
    ⟨(p.2 : G) * (p.1 : G),
      Subgroup.mul_mem _ (Subgroup.mem_sup_left p.2.2) (Subgroup.mem_sup_right p.1.2)⟩
  have hg : Function.Injective g := by
    rintro ⟨c, b⟩ ⟨c', b'⟩ h
    have h' : (b : G) * (c : G) = (b' : G) * (c' : G) := congrArg Subtype.val h
    have hmem : (b' : G)⁻¹ * (b : G) ∈ Subgroup.zpowers x ⊓ B := by
      have e : (b' : G)⁻¹ * (b : G) = (c' : G) * (c : G)⁻¹ := by
        have : (b : G) = (b' : G) * (c' : G) * (c : G)⁻¹ := by
          rw [← h']; simp [mul_assoc]
        rw [this]; simp [mul_assoc]
      refine ⟨?_, ?_⟩
      · rw [e]; exact Subgroup.mul_mem _ c'.2 (Subgroup.inv_mem _ c.2)
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ b'.2) b.2
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hbb : (b : G) = b' := by
      have := congrArg (fun t => (b' : G) * t) hmem
      simpa using this
    have hcc : (c : G) = c' := by
      rw [hbb] at h'
      exact mul_left_cancel h'
    have hbb' : b = b' := Subtype.ext hbb
    have hcc' : c = c' := Subtype.ext hcc
    rw [hbb', hcc']
  calc f * Nat.card B = Nat.card (Subgroup.zpowers x × B) := by
        rw [Nat.card_prod, hcard]
    _ ≤ Nat.card (B ⊔ Subgroup.zpowers x : Subgroup G) := Nat.card_le_card_of_injective g hg

theorem orderFive_arith {f z j b : ℕ} (hf : 2 ≤ f) (hz : 1 ≤ z) (h1 : z * f ^ j ≤ b)
    (h2 : b ≤ f ^ 3) : z ^ j * b ≤ f ^ 5 := by
  have hf0 : 0 < f := by omega
  have hj : j ≤ 3 := by
    by_contra hj
    replace hj : 4 ≤ j := by omega
    have h3 : f ^ 4 ≤ f ^ j := Nat.pow_le_pow_right hf0 hj
    have h4 : f ^ 3 < f ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    have h5 : f ^ j ≤ z * f ^ j := Nat.le_mul_of_pos_left _ hz
    omega
  have hb5 : b ≤ f ^ 5 := h2.trans (Nat.pow_le_pow_right hf0 (by norm_num))
  interval_cases j
  · simpa using hb5
  · have hz2 : z ≤ f ^ 2 := by
      have : z * f ≤ f ^ 2 * f := by
        calc z * f ≤ b := by simpa using h1
          _ ≤ f ^ 3 := h2
          _ = f ^ 2 * f := by ring
      exact Nat.le_of_mul_le_mul_right this hf0
    calc z ^ 1 * b ≤ f ^ 2 * f ^ 3 := Nat.mul_le_mul (by simpa using hz2) h2
      _ = f ^ 5 := by ring
  · have hz2 : z ≤ f := by
      have : z * f ^ 2 ≤ f * f ^ 2 := by
        calc z * f ^ 2 ≤ b := h1
          _ ≤ f ^ 3 := h2
          _ = f * f ^ 2 := by ring
      exact Nat.le_of_mul_le_mul_right this (by positivity)
    calc z ^ 2 * b ≤ f ^ 2 * f ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_left hz2 2) h2
      _ = f ^ 5 := by ring
  · have hz2 : z ≤ 1 := by
      have : z * f ^ 3 ≤ 1 * f ^ 3 := by
        calc z * f ^ 3 ≤ b := h1
          _ ≤ f ^ 3 := h2
          _ = 1 * f ^ 3 := by ring
      exact Nat.le_of_mul_le_mul_right this (by positivity)
    have hz1 : z = 1 := le_antisymm hz2 hz
    subst hz1
    simpa using hb5

theorem orderFive_aux {f : ℕ} (hf : f.Prime) (hexp : ∀ x : G, x ^ f = 1)
    (hcl : ∀ x y w : G, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    (hrank : ∀ E : Subgroup G, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E ≤ f ^ 3) :
    ∀ n j : ℕ, 4 ≤ j + n → ∀ B : Subgroup G, (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
      f ^ j * Nat.card (Subgroup.center G) ≤ Nat.card B →
      (Subgroup.centralizer (B : Set G)).index ≤ Nat.card (Subgroup.center G) ^ j →
      Nat.card G ≤ f ^ 5 := by
  have hz : 0 < Nat.card (Subgroup.center G) := Nat.card_pos
  intro n
  induction n with
  | zero =>
    intro j hj B hB h1 _
    exfalso
    have h3 := hrank B hB
    have h4 : f ^ 4 ≤ f ^ j := Nat.pow_le_pow_right hf.pos (by omega)
    have h5 : f ^ 3 < f ^ 4 := Nat.pow_lt_pow_right hf.one_lt (by norm_num)
    have h6 : f ^ j ≤ f ^ j * Nat.card (Subgroup.center G) := Nat.le_mul_of_pos_right _ hz
    omega
  | succ n ih =>
    intro j hj B hB h1 h2
    by_cases hcB : Subgroup.centralizer (B : Set G) ≤ B
    · have hBc : B ≤ Subgroup.centralizer (B : Set G) := by
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact hB u hu b hb
      have heq : Subgroup.centralizer (B : Set G) = B := le_antisymm hcB hBc
      have hG : Nat.card G = (Subgroup.centralizer (B : Set G)).index * Nat.card B := by
        rw [← Subgroup.index_mul_card (Subgroup.centralizer (B : Set G)), heq]
      rw [hG]
      calc (Subgroup.centralizer (B : Set G)).index * Nat.card B
          ≤ Nat.card (Subgroup.center G) ^ j * Nat.card B := Nat.mul_le_mul_right _ h2
        _ ≤ f ^ 5 := orderFive_arith hf.two_le hz (by rw [mul_comm]; exact h1) (hrank B hB)
    · rw [SetLike.not_le_iff_exists] at hcB
      obtain ⟨x, hxC, hxB⟩ := hcB
      have hxc : ∀ b ∈ B, b * x = x * b := by
        intro b hb
        rw [Subgroup.mem_centralizer_iff] at hxC
        exact hxC b hb
      refine ih (j + 1) (by omega) (B ⊔ Subgroup.zpowers x) (orderFive_sup_abelian hB hxc) ?_ ?_
      · calc f ^ (j + 1) * Nat.card (Subgroup.center G)
            = f * (f ^ j * Nat.card (Subgroup.center G)) := by ring
          _ ≤ f * Nat.card B := Nat.mul_le_mul_left f h1
          _ ≤ Nat.card (B ⊔ Subgroup.zpowers x : Subgroup G) := orderFive_card_sup hf (hexp x) hxB
      · calc (Subgroup.centralizer ((B ⊔ Subgroup.zpowers x : Subgroup G) : Set G)).index
            ≤ (Subgroup.centralizer (B : Set G)).index * Nat.card (Subgroup.center G) :=
              orderFive_index_sup_le hcl B x
          _ ≤ Nat.card (Subgroup.center G) ^ j * Nat.card (Subgroup.center G) :=
              Nat.mul_le_mul_right _ h2
          _ = Nat.card (Subgroup.center G) ^ (j + 1) := (pow_succ _ _).symm

theorem orderFive_main {f : ℕ} (hf : f.Prime) (hexp : ∀ x : G, x ^ f = 1)
    (hcl : ∀ x y w : G, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    (hrank : ∀ E : Subgroup G, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E ≤ f ^ 3) :
    Nat.card G ≤ f ^ 5 := by
  refine orderFive_aux hf hexp hcl hrank 4 0 (by norm_num) (Subgroup.center G) ?_ (by simp) ?_
  · intro a _ b hb
    exact Subgroup.mem_center_iff.mp hb a
  · have : Subgroup.centralizer ((Subgroup.center G : Subgroup G) : Set G) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr subset_rfl
    rw [this, Subgroup.index_top]
    simp

end orderFive

theorem card_le_pow_five {f : ℕ} (hf : f.Prime) {Ω : Subgroup K} (hexp : ∀ x ∈ Ω, x ^ f = 1)
    (hcl : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ w ∈ Ω, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    (hrank : ∀ E : Subgroup K, E ≤ Ω → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E ≤ f ^ 3) : Nat.card Ω ≤ f ^ 5 := by
  refine orderFive_main hf (G := Ω) ?_ ?_ ?_
  · intro x
    exact Subtype.ext (by simpa using hexp x x.2)
  · intro x y w
    apply Subtype.ext
    simpa [commutatorElement_def] using hcl x x.2 y y.2 w w.2
  · intro E hE
    have hE' : ∀ a ∈ E.map Ω.subtype, ∀ b ∈ E.map Ω.subtype, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      have := hE a' ha' b' hb'
      simpa using congrArg Subtype.val this
    have := hrank (E.map Ω.subtype) (Subgroup.map_subtype_le E) hE'
    rwa [Subgroup.card_map_of_injective Subtype.val_injective] at this
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

section rankFive

theorem rankFive_exists_powHom {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) {P : Subgroup K}
    (hP' : ∀ x ∈ P, ∀ y ∈ P, ∀ w ∈ P, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    (hPf : ∀ x ∈ P, ∀ w ∈ P, w * x ^ f = x ^ f * w) :
    ∃ Φ : ↥P →* ↥P, ∀ x : ↥P, (Φ x : K) = (x : K) ^ f := by
  refine ⟨MonoidHom.mk' (fun x : ↥P => x ^ f) (fun a b => ?_), fun x => rfl⟩
  apply Subtype.ext
  have := pow_mul_of_central hf hf2 hP' hPf a.2 b.2
  simpa using this

theorem rankFive_card_ker_le {f : ℕ} (hf : f.Prime) {P : Subgroup K}
    (hP' : ∀ x ∈ P, ∀ y ∈ P, ∀ w ∈ P, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    (hrank : ∀ E : Subgroup K, E ≤ P → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ f = 1) → Nat.card E ≤ f ^ 3)
    (Φ : ↥P →* ↥P) (hΦ : ∀ x : ↥P, (Φ x : K) = (x : K) ^ f) : Nat.card Φ.ker ≤ f ^ 5 := by
  have hΩP : Φ.ker.map P.subtype ≤ P := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hexp : ∀ x ∈ Φ.ker.map P.subtype, x ^ f = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hΦ y
    rw [MonoidHom.mem_ker.mp hy] at h
    simpa using h.symm
  have hcl : ∀ x ∈ Φ.ker.map P.subtype, ∀ y ∈ Φ.ker.map P.subtype,
      ∀ w ∈ Φ.ker.map P.subtype, w * ⁅x, y⁆ = ⁅x, y⁆ * w := fun x hx y hy w hw =>
    hP' x (hΩP hx) y (hΩP hy) w (hΩP hw)
  have hrank' : ∀ E : Subgroup K, E ≤ Φ.ker.map P.subtype →
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E ≤ f ^ 3 :=
    fun E hE hab => hrank E (hE.trans hΩP) hab (fun a ha => hexp a (hE ha))
  have h5 := card_le_pow_five hf hexp hcl hrank'
  rwa [Subgroup.card_subtype] at h5

theorem rankFive_card_range_le {G H : Type} [Group G] [Finite G] [Group H] (Φ : G →* G)
    (Ψ : G →* H) (h : Φ.range ≤ Ψ.ker) : Nat.card Ψ.range ≤ Nat.card Φ.ker := by
  have h1 : Nat.card Φ.ker * Nat.card Φ.range = Nat.card G := Subgroup.card_ker_mul_card_range Φ
  have h2 : Nat.card Ψ.ker * Nat.card Ψ.range = Nat.card G := Subgroup.card_ker_mul_card_range Ψ
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le h
  have hpos : 0 < Nat.card Φ.range := Nat.card_pos
  have hpos2 : 0 < Nat.card Ψ.ker := Nat.card_pos
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · exact h0
  have key : Nat.card Φ.ker = m * Nat.card Ψ.range := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card Φ.ker * Nat.card Φ.range = Nat.card G := h1
      _ = Nat.card Ψ.ker * Nat.card Ψ.range := h2.symm
      _ = m * Nat.card Ψ.range * Nat.card Φ.range := by rw [hm]; ring
  rw [key]
  exact Nat.le_mul_of_pos_left _ hm0

theorem rankFive_nsmul_eq_zero {f : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod f) W] (w : W) :
    f • w = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod f), ZMod.natCast_self, zero_smul]

end rankFive

theorem finrank_le_five {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) {P : Subgroup K} (hP : IsPGroup f P)
    (hP' : ∀ x ∈ P, ∀ y ∈ P, ∀ w ∈ P, w * ⁅x, y⁆ = ⁅x, y⁆ * w)
    (hPf : ∀ x ∈ P, ∀ w ∈ P, w * x ^ f = x ^ f * w)
    (hrank : ∀ E : Subgroup K, E ≤ P → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      (∀ a ∈ E, a ^ f = 1) → Nat.card E ≤ f ^ 3)
    {W : Type} [AddCommGroup W] [Module (ZMod f) W] [Module.Finite (ZMod f) W] (π : K → W)
    (hπ : ∀ x ∈ P, ∀ y ∈ P, π (x * y) = π x + π y) (L : Submodule (ZMod f) W)
    (hL : ∀ w ∈ L, ∃ x ∈ P, π x = w) : Module.finrank (ZMod f) L ≤ 5 := by
  have hf : f.Prime := Fact.out
  obtain ⟨Φ, hΦ⟩ := rankFive_exists_powHom hf hf2 hP' hPf
  have hker : Nat.card Φ.ker ≤ f ^ 5 := rankFive_card_ker_le hf hP' hrank Φ hΦ
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥P →* Multiplicative W, ∀ x : ↥P, Ψ x = Multiplicative.ofAdd (π x) :=
    ⟨MonoidHom.mk' (fun x : ↥P => Multiplicative.ofAdd (π x)) (fun a b => by
        show Multiplicative.ofAdd (π ((a : K) * b)) = _
        rw [hπ a a.2 b b.2]
        rfl), fun x => rfl⟩
  have hrange : Φ.range ≤ Ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    have h1 : Φ x = x ^ f := Subtype.ext (hΦ x)
    rw [h1, map_pow, hΨ, ← ofAdd_nsmul, rankFive_nsmul_eq_zero]
    rfl
  have hle := rankFive_card_range_le Φ Ψ hrange
  have hLle : Nat.card L ≤ Nat.card Ψ.range := by
    haveI : Finite Ψ.range := Finite.of_surjective _ Ψ.rangeRestrict_surjective
    let g : L → Ψ.range := fun w => ⟨Multiplicative.ofAdd (w : W), by
      obtain ⟨x, hx, hxw⟩ := hL w w.2
      exact ⟨⟨x, hx⟩, by rw [hΨ]; simp [hxw]⟩⟩
    refine Nat.card_le_card_of_injective g ?_
    intro a b hab
    have h0 : (g a : Multiplicative W) = (g b : Multiplicative W) := by rw [hab]
    have h : Multiplicative.ofAdd (a : W) = Multiplicative.ofAdd (b : W) := h0
    exact Subtype.ext (Multiplicative.ofAdd.injective h)
  haveI : Finite W := Module.finite_of_finite (ZMod f)
  have hcardL : Nat.card L = f ^ Module.finrank (ZMod f) L := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod f), Nat.card_zmod]
  have hpow : f ^ Module.finrank (ZMod f) L ≤ f ^ 5 :=
    calc f ^ Module.finrank (ZMod f) L = Nat.card L := hcardL.symm
      _ ≤ Nat.card Ψ.range := hLle
      _ ≤ Nat.card Φ.ker := hle
      _ ≤ f ^ 5 := hker
  exact (Nat.pow_le_pow_iff_right hf.one_lt).mp hpow
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem commutator_pow_le_frattini {f : ℕ} [Fact f.Prime] {C : Subgroup K} (hC : IsPGroup f C) :
    ((⁅C, C⁆ ⊔ Subgroup.closure {x : K | ∃ y ∈ C, x = y ^ f}).subgroupOf C) ≤ frattini ↥C := by
  haveI : Fact (IsPGroup f ↥C) := ⟨hC⟩
  have hle : (⁅C, C⁆ ⊔ Subgroup.closure {x : K | ∃ y ∈ C, x = y ^ f}) ≤
      (frattini ↥C).map C.subtype := by
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      refine ⟨⁅(⟨a, ha⟩ : ↥C), ⟨b, hb⟩⁆, ?_, rfl⟩
      exact CFSG.commutator_le_frattini_of_isPGroup (R := ↥C) (p := f)
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    · rw [Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨(⟨y, hy⟩ : ↥C) ^ f,
        CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥C) (p := f) _, rfl⟩
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hle (Subgroup.mem_subgroupOf.mp hx)
  have : y = x := Subtype.ext hyx
  subst this
  exact hy

theorem frattini_zpow_eq_one_or {t : K} (ht2 : t ^ 2 = 1) (n : ℤ) : t ^ n = 1 ∨ t ^ n = t := by
  have hn : n = 2 * (n / 2) + n % 2 := (Int.mul_ediv_add_emod n 2).symm
  have h2 : t ^ (2 : ℤ) = 1 := by simpa using ht2
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [hn, h, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [hn, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem frattini_isPGroup_zpowers {t : K} (ht2 : t ^ 2 = 1) : IsPGroup 2 (zpowers t) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have h2 : t ^ (2 : ℤ) = 1 := by simpa using ht2
  change (g : K) ^ (2 ^ 1) = 1
  rw [← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simpa using congrArg (fun a => a ^ n) h2

theorem eq_of_trivial_on_quotient {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) {C M₀ : Subgroup K}
    (hC : IsPGroup f C) (hM : M₀ ≤ C) (hMn : ∀ x ∈ C, ∀ m ∈ M₀, x * m * x⁻¹ ∈ M₀)
    (hfr : M₀.subgroupOf C ≤ frattini ↥C) {t : K} (ht2 : t ^ 2 = 1)
    (htC : t ∈ normalizer (C : Set K)) (htM : t ∈ normalizer (M₀ : Set K))
    (htriv : ∀ x ∈ C, x⁻¹ * (t * x * t⁻¹) ∈ M₀) : ∀ x ∈ C, t * x = x * t := by
  have hM0 : IsPGroup f M₀ := hC.to_le hM
  have hq : ¬ 2 ∣ Nat.card M₀ := by
    obtain ⟨n, hn⟩ := hM0.exists_card_eq
    rw [hn]
    intro h
    exact hf2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : f.Prime)).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have hex : ∀ x ∈ C, ∃ m ∈ M₀, t * (x * m) * t⁻¹ = x * m := by
    intro x hx
    obtain ⟨m, hm, hfix⟩ := exists_fixed_in_coset (q := 2) (frattini_isPGroup_zpowers ht2)
      (zpowers_le.mpr htM) hq (x := x) (by
        intro s hs
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
        rcases frattini_zpow_eq_one_or ht2 n with h | h
        · rw [h]; simpa using M₀.one_mem
        · rw [h]; exact htriv x hx)
    exact ⟨m, hm, hfix t (mem_zpowers t)⟩
  let H : Subgroup ↥C := (centralizer ({t} : Set K)).subgroupOf C
  have hsup : H ⊔ frattini ↥C = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨m, hm, hfix⟩ := hex g g.2
    have hmC : m ∈ C := hM hm
    have h1 : (⟨(g : K) * m, C.mul_mem g.2 hmC⟩ : ↥C) ∈ H := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      change (g : K) * m * t = t * ((g : K) * m)
      calc (g : K) * m * t = t * (g * m) * t⁻¹ * t := by rw [hfix]
        _ = t * ((g : K) * m) := by group
    have h2 : (⟨m, hmC⟩ : ↥C)⁻¹ ∈ frattini ↥C :=
      inv_mem (hfr (Subgroup.mem_subgroupOf.mpr hm))
    have hg : g = (⟨(g : K) * m, C.mul_mem g.2 hmC⟩ : ↥C) * (⟨m, hmC⟩ : ↥C)⁻¹ := by
      apply Subtype.ext
      simp
    rw [hg]
    exact Subgroup.mul_mem_sup h1 h2
  have htop : H = ⊤ := frattini_nongenerating hsup
  intro x hx
  have hxH : (⟨x, hx⟩ : ↥C) ∈ H := by rw [htop]; exact Subgroup.mem_top _
  have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hxH)
  exact this.symm

theorem frattini_commute_of_commutator {x c t : K} (hct : t * c = c * t)
    (hdt : t * ⁅x, c⁆ = ⁅x, c⁆ * t) :
    c * (x⁻¹ * (t * x * t⁻¹)) = (x⁻¹ * (t * x * t⁻¹)) * c := by
  have hcc : t * c * t⁻¹ = c := by rw [hct]; group
  have hcinv : t * c⁻¹ * t⁻¹ = c⁻¹ := by
    have : t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ := by group
    rw [this, hcc]
  have hd' : t * ⁅x, c⁆ * t⁻¹ = ⁅x, c⁆ := by rw [hdt]; group
  have e : t * ⁅x, c⁆ * t⁻¹ =
      (t * x * t⁻¹) * (t * c * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * c⁻¹ * t⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, hcc, hcinv, commutatorElement_def] at hd'
  have h3 : (t * x * t⁻¹) * c * (t * x * t⁻¹)⁻¹ = x * c * x⁻¹ := mul_right_cancel hd'
  have h4 : (x⁻¹ * (t * x * t⁻¹)) * c * (x⁻¹ * (t * x * t⁻¹))⁻¹ = c := by
    calc (x⁻¹ * (t * x * t⁻¹)) * c * (x⁻¹ * (t * x * t⁻¹))⁻¹
        = x⁻¹ * ((t * x * t⁻¹) * c * (t * x * t⁻¹)⁻¹) * x := by group
      _ = x⁻¹ * (x * c * x⁻¹) * x := by rw [h3]
      _ = c := by group
  exact (mul_inv_eq_iff_eq_mul.mp h4).symm

theorem frattini_conj_inv {x t : K} (htt : t * t = 1) :
    t * (x⁻¹ * (t * x * t⁻¹)) * t⁻¹ = (x⁻¹ * (t * x * t⁻¹))⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htt' : t⁻¹ * t⁻¹ = 1 := by rw [htinv]; exact htt
  calc t * (x⁻¹ * (t * x * t⁻¹)) * t⁻¹
      = (t * x⁻¹ * t⁻¹) * ((t * t) * x * (t⁻¹ * t⁻¹)) := by group
    _ = (t * x⁻¹ * t⁻¹) * x := by rw [htt, htt']; group
    _ = (x⁻¹ * (t * x * t⁻¹))⁻¹ := by group

theorem frattini_eq_one_of_sq_eq_one {G : Type*} [Group G] {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2)
    (hG : IsPGroup f G) {y : G} (hy : y ^ 2 = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hG y
  have hd : f ^ k ∣ 2 := hk ▸ orderOf_dvd_of_pow_eq_one hy
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact orderOf_eq_one_iff.mp (by rw [hk, h])
  · exfalso
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at h
    · have : f ∣ 2 := h ▸ dvd_pow_self f hk0.ne'
      exact hf2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)

theorem centralizes_of_critical {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) {X : Subgroup K}
    (hX : IsPGroup f X) (C₀ : Subgroup ↥X) (hC₀ : CFSG.SectionRank.Ccomm.IsThompsonCritical C₀)
    {t : K} (ht2 : t ^ 2 = 1) (htX : t ∈ normalizer (X : Set K))
    (htC : ∀ x ∈ C₀.map X.subtype, t * x = x * t) : ∀ x ∈ X, t * x = x * t := by
  obtain ⟨-, -, hcomm, hcent⟩ := hC₀
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  intro x hx
  have huX : t * x * t⁻¹ ∈ X := (mem_normalizer_iff.mp htX x).mp hx
  have hyX : x⁻¹ * (t * x * t⁻¹) ∈ X := X.mul_mem (X.inv_mem hx) huX
  have htC' : ∀ c ∈ C₀, t * (c : K) = (c : K) * t := fun c hc => htC c ⟨c, hc, rfl⟩
  have hyc : (⟨x⁻¹ * (t * x * t⁻¹), hyX⟩ : ↥X) ∈ centralizer (C₀ : Set ↥X) := by
    rw [mem_centralizer_iff]
    intro c hc
    apply Subtype.ext
    have hd : ⁅(⟨x, hx⟩ : ↥X), c⁆ ∈ C₀ :=
      (hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hc)).1
    have hdt : t * ⁅x, (c : K)⁆ = ⁅x, (c : K)⁆ * t := htC' _ hd
    exact frattini_commute_of_commutator (htC' c hc) hdt
  have hyC : (⟨x⁻¹ * (t * x * t⁻¹), hyX⟩ : ↥X) ∈ C₀ := (hcent.le hyc).1
  have hyt : t * (x⁻¹ * (t * x * t⁻¹)) = (x⁻¹ * (t * x * t⁻¹)) * t := htC' _ hyC
  have hy1 : x⁻¹ * (t * x * t⁻¹) = (x⁻¹ * (t * x * t⁻¹))⁻¹ := by
    rw [← frattini_conj_inv htt, hyt]; group
  have hysq : (⟨x⁻¹ * (t * x * t⁻¹), hyX⟩ : ↥X) ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    exact mul_eq_one_iff_eq_inv.mpr hy1
  have hy : (⟨x⁻¹ * (t * x * t⁻¹), hyX⟩ : ↥X) = 1 := frattini_eq_one_of_sq_eq_one hf2 hX hysq
  have hy1' : x⁻¹ * (t * x * t⁻¹) = 1 := congrArg Subtype.val hy
  have hx' : x = t * x * t⁻¹ := inv_mul_eq_one.mp hy1'
  calc t * x = t * x * t⁻¹ * t := by group
    _ = x * t := by rw [← hx']
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem critSection_mem_normalizer {H : Subgroup K} {g : K} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ normalizer (H : Set K) := by
  rw [mem_normalizer_iff]
  intro x
  exact ⟨h1 x, fun hx => by simpa [mul_assoc] using h2 _ hx⟩

theorem critSection_conj_mem {X : Subgroup K} {C₀ : Subgroup ↥X} (hC₀ : C₀.Characteristic) {g : K}
    (hg : g ∈ normalizer (X : Set K)) {c : K} (hc : c ∈ C₀.map X.subtype) :
    g * c * g⁻¹ ∈ C₀.map X.subtype := by
  obtain ⟨c₀, hc₀, rfl⟩ := Subgroup.mem_map.mp hc
  have h := CFSG.SectionRank.Ccomm.char_apply_mem hC₀ (X.normalizerMonoidHom ⟨g, hg⟩) hc₀
  exact Subgroup.mem_map.mpr ⟨_, h, rfl⟩

theorem critSection_normalizes_critical {X G : Subgroup K} (hG : G ≤ normalizer (X : Set K))
    {C₀ : Subgroup ↥X} (hC₀ : C₀.Characteristic) {g : K} (hg : g ∈ G) :
    g ∈ normalizer ((C₀.map X.subtype : Subgroup K) : Set K) :=
  critSection_mem_normalizer (fun _ hx => critSection_conj_mem hC₀ (hG hg) hx)
    (fun _ hx => by simpa using critSection_conj_mem hC₀ (hG (inv_mem hg)) hx)

theorem critSection_M0_conj_mem {f : ℕ} {C : Subgroup K} {g : K} (hg : g ∈ normalizer (C : Set K))
    {m : K} (hm : m ∈ (⁅C, C⁆ ⊔ Subgroup.closure {x : K | ∃ y ∈ C, x = y ^ f})) :
    g * m * g⁻¹ ∈ (⁅C, C⁆ ⊔ Subgroup.closure {x : K | ∃ y ∈ C, x = y ^ f}) := by
  have hC : ∀ x ∈ C, g * x * g⁻¹ ∈ C := fun x hx => (mem_normalizer_iff.mp hg x).mp hx
  have key : (⁅C, C⁆ ⊔ Subgroup.closure {x : K | ∃ y ∈ C, x = y ^ f}) ≤
      (⁅C, C⁆ ⊔ Subgroup.closure {x : K | ∃ y ∈ C, x = y ^ f}).comap
        (MulAut.conj g).toMonoidHom := by
    refine sup_le ?_ ?_
    · rw [commutator_le]
      intro a ha b hb
      have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
      exact mem_sup_left (commutator_mem_commutator (hC a ha) (hC b hb))
    · rw [closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← conj_pow]
      exact mem_sup_right (subset_closure ⟨_, hC y hy, rfl⟩)
  exact key hm

theorem critSection_comm_central {X : Subgroup K} {C₀ : Subgroup ↥X}
    (hC₀ : CFSG.SectionRank.Ccomm.IsThompsonCritical C₀) {x y w : K}
    (hx : x ∈ C₀.map X.subtype) (hy : y ∈ C₀.map X.subtype) (hw : w ∈ C₀.map X.subtype) :
    w * ⁅x, y⁆ = ⁅x, y⁆ * w := by
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
  have h1 : ⁅x₀, y₀⁆ ∈ ⁅(⊤ : Subgroup ↥X), C₀⁆ := commutator_mem_commutator (mem_top _) hy₀
  have h2 : ⁅x₀, y₀⁆ ∈ centralizer (C₀ : Set ↥X) := (hC₀.2.2.1 h1).2
  rw [mem_centralizer_iff] at h2
  have h3 := congrArg X.subtype (h2 w₀ hw₀)
  simp only [map_mul, map_commutatorElement] at h3
  exact h3

theorem critSection_pow_central {f : ℕ} [Fact f.Prime] {X : Subgroup K} (hX : IsPGroup f X)
    {C₀ : Subgroup ↥X} (hC₀ : CFSG.SectionRank.Ccomm.IsThompsonCritical C₀) {x w : K}
    (hx : x ∈ C₀.map X.subtype) (hw : w ∈ C₀.map X.subtype) : w * x ^ f = x ^ f * w := by
  haveI : Fact (IsPGroup f ↥C₀) := ⟨hX.to_subgroup C₀⟩
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
  have h1 : (⟨x₀, hx₀⟩ : ↥C₀) ^ f ∈ frattini ↥C₀ :=
    CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥C₀) (p := f) _
  have h2 : C₀.subtype ((⟨x₀, hx₀⟩ : ↥C₀) ^ f) ∈ centralizer (C₀ : Set ↥X) :=
    (hC₀.2.1 (Subgroup.mem_map_of_mem C₀.subtype h1)).2
  rw [mem_centralizer_iff] at h2
  have h3 := congrArg X.subtype (h2 w₀ hw₀)
  simpa using h3

theorem exists_critical_section {p f : ℕ} {S X N : Subgroup K} {z : K} (h : Setup628 p f S X N z)
    {R : Subgroup K} (hRS : R ≤ S) {t : K} (htR : t ∈ R) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ (C M₀ : Subgroup K) (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod f) W)
      (_ : Module.Finite (ZMod f) W) (π : K → W) (ρ : Representation (ZMod f) ↥R W),
      C ≤ X ∧ M₀ ≤ C ∧ (∀ g ∈ R, g ∈ normalizer (C : Set K)) ∧
      (∀ g ∈ R, g ∈ normalizer (M₀ : Set K)) ∧
      (∀ x ∈ C, ∀ y ∈ C, ∀ w ∈ C, w * ⁅x, y⁆ = ⁅x, y⁆ * w) ∧
      (∀ x ∈ C, ∀ w ∈ C, w * x ^ f = x ^ f * w) ∧
      (∀ x ∈ C, ∀ y ∈ C, π (x * y) = π x + π y) ∧ (∀ x ∈ C, π x = 0 ↔ x ∈ M₀) ∧
      (∀ w : W, ∃ x ∈ C, π x = w) ∧ (∀ (g : ↥R), ∀ x ∈ C, ρ g (π x) = π (g * x * g⁻¹)) ∧
      (∃ w : W, ρ ⟨t, htR⟩ w ≠ w) := by
  haveI : Fact f.Prime := ⟨h.hf⟩
  obtain ⟨⟨C₀, hC₀⟩, -⟩ := CFSG.SectionRank.Ccomm.thompson_critical_subgroup (p := f) h.hX
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup K, C = C₀.map X.subtype := ⟨_, rfl⟩
  have hRX : R ≤ normalizer (X : Set K) := fun g hg => h.hSX (mem_sup_left (hRS hg))
  have hCX : C ≤ X := hCdef ▸ Subgroup.map_subtype_le C₀
  have hCp : IsPGroup f ↥C := h.hX.to_le hCX
  have hRC : ∀ g ∈ R, g ∈ normalizer (C : Set K) := fun g hg =>
    hCdef ▸ critSection_normalizes_critical hRX hC₀.1 hg
  have hcent1 : ∀ x ∈ C, ∀ y ∈ C, ∀ w ∈ C, w * ⁅x, y⁆ = ⁅x, y⁆ * w := fun x hx y hy w hw => by
    subst hCdef
    exact critSection_comm_central hC₀ hx hy hw
  have hcent2 : ∀ x ∈ C, ∀ w ∈ C, w * x ^ f = x ^ f * w := fun x hx w hw => by
    subst hCdef
    exact critSection_pow_central h.hX hC₀ hx hw
  set M₀ : Subgroup K := ⁅C, C⁆ ⊔ Subgroup.closure {x : K | ∃ y ∈ C, x = y ^ f}
  have hM₀C : M₀ ≤ C := by
    refine sup_le (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb)
    · rw [Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      exact C.pow_mem hy f
  have hMn : ∀ x ∈ C, ∀ m ∈ M₀, x * m * x⁻¹ ∈ M₀ := fun x hx m hm =>
    critSection_M0_conj_mem (Subgroup.le_normalizer hx) hm
  have hRM : ∀ g ∈ R, g ∈ normalizer (M₀ : Set K) := fun g hg =>
    critSection_mem_normalizer (fun _ hx => critSection_M0_conj_mem (hRC g hg) hx)
      (fun _ hx => by simpa using critSection_M0_conj_mem (hRC g⁻¹ (inv_mem hg)) hx)
  obtain ⟨W, iA, iM, iF, π, ρ, hadd, hker, hsurj, hπρ⟩ :=
    exists_elemSection (f := f) (Y := C) (M := M₀) (G := R) hM₀C hMn
      (fun x hx y hy => mem_sup_left (commutator_mem_commutator hx hy))
      (fun x hx => mem_sup_right (subset_closure ⟨x, hx, rfl⟩)) hRC hRM
  have hnt : ∃ w : W, ρ ⟨t, htR⟩ w ≠ w := by
    by_contra hcon'
    have hcon : ∀ w : W, ρ ⟨t, htR⟩ w = w := fun w => not_not.mp fun hne => hcon' ⟨w, hne⟩
    have h0 : π 1 = 0 := (hker 1 C.one_mem).mpr M₀.one_mem
    have htriv : ∀ x ∈ C, x⁻¹ * (t * x * t⁻¹) ∈ M₀ := by
      intro x hx
      have htxC : t * x * t⁻¹ ∈ C := (mem_normalizer_iff.mp (hRC t htR) x).mp hx
      have h1 : π (t * x * t⁻¹) = π x := by
        have h1' := hπρ ⟨t, htR⟩ x hx
        rw [hcon (π x)] at h1'
        exact h1'.symm
      have h2 : π (x⁻¹ * x) = π x⁻¹ + π x := hadd x⁻¹ (C.inv_mem hx) x hx
      rw [inv_mul_cancel, h0] at h2
      have h3 : π (x⁻¹ * (t * x * t⁻¹)) = 0 := by
        rw [hadd _ (C.inv_mem hx) _ htxC, h1]
        exact h2.symm
      exact (hker _ (C.mul_mem (C.inv_mem hx) htxC)).mp h3
    have hcomm : ∀ x ∈ C, t * x = x * t :=
      eq_of_trivial_on_quotient h.hf2 hCp hM₀C hMn (commutator_pow_le_frattini hCp) ht2
        (hRC t htR) (hRM t htR) htriv
    have hXc : ∀ x ∈ X, t * x = x * t :=
      centralizes_of_critical h.hf2 h.hX C₀ hC₀ ht2 (hRX htR) (hCdef ▸ hcomm)
    exact ht1 (centralizer_S_X h t (hRS htR) hXc)
  exact ⟨C, M₀, W, iA, iM, iF, π, ρ, hCX, hM₀C, hRC, hRM, hcent1, hcent2, hadd, hker, hsurj, hπρ,
    hnt⟩
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem fixedSpace_apply_apply_t {R : Subgroup K} {t : K} (hR : IsExt2 R t) {f : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod f) W] (ρ : Representation (ZMod f) ↥R W) (w : W) :
    ρ ⟨t, hR.t_mem⟩ (ρ ⟨t, hR.t_mem⟩ w) = w := by
  have h : (⟨t, hR.t_mem⟩ : ↥R) * ⟨t, hR.t_mem⟩ = 1 := by
    apply Subtype.ext
    simpa [sq] using hR.t_sq
  calc ρ ⟨t, hR.t_mem⟩ (ρ ⟨t, hR.t_mem⟩ w)
      = (ρ ((⟨t, hR.t_mem⟩ : ↥R) * ⟨t, hR.t_mem⟩)) w := by rw [map_mul]; rfl
    _ = w := by rw [h, map_one]; rfl

theorem fixedSpace_comm_t {R : Subgroup K} {t : K} (hR : IsExt2 R t) {f : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod f) W] (ρ : Representation (ZMod f) ↥R W) (g : ↥R) (w : W) :
    ρ ⟨t, hR.t_mem⟩ (ρ g w) = ρ g (ρ ⟨t, hR.t_mem⟩ w) := by
  have h : (⟨t, hR.t_mem⟩ : ↥R) * g = g * ⟨t, hR.t_mem⟩ :=
    Subtype.ext (hR.t_comm g g.2).symm
  calc ρ ⟨t, hR.t_mem⟩ (ρ g w) = (ρ ((⟨t, hR.t_mem⟩ : ↥R) * g)) w := by rw [map_mul]; rfl
    _ = (ρ (g * ⟨t, hR.t_mem⟩)) w := by rw [h]
    _ = ρ g (ρ ⟨t, hR.t_mem⟩ w) := by rw [map_mul]; rfl

theorem fixedSpace_exists_sub {R : Subgroup K} {t : K} (hR : IsExt2 R t) {f : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod f) W] (ρ : Representation (ZMod f) ↥R W)
    (hnt : ∃ w : W, ρ ⟨t, hR.t_mem⟩ w ≠ w) :
    ∃ U : Submodule (ZMod f) W, Nontrivial U ∧ (∀ g : ↥R, ∀ u ∈ U, ρ g u ∈ U) ∧
      ∀ u ∈ U, ρ ⟨t, hR.t_mem⟩ u = -u := by
  have hmem : ∀ u : W, u ∈ LinearMap.ker (ρ ⟨t, hR.t_mem⟩ + 1) ↔ ρ ⟨t, hR.t_mem⟩ u = -u := by
    intro u
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
    exact add_eq_zero_iff_eq_neg
  refine ⟨LinearMap.ker (ρ ⟨t, hR.t_mem⟩ + 1), ?_, ?_, fun u hu => (hmem u).1 hu⟩
  · obtain ⟨w₀, hw₀⟩ := hnt
    have hu : ρ ⟨t, hR.t_mem⟩ (w₀ - ρ ⟨t, hR.t_mem⟩ w₀) = -(w₀ - ρ ⟨t, hR.t_mem⟩ w₀) := by
      rw [map_sub, fixedSpace_apply_apply_t hR ρ w₀, neg_sub]
    refine ⟨⟨⟨w₀ - ρ ⟨t, hR.t_mem⟩ w₀, (hmem _).2 hu⟩, 0, ?_⟩⟩
    intro h
    exact hw₀ (sub_eq_zero.1 (congrArg Subtype.val h)).symm
  · intro g u hu
    rw [hmem] at hu ⊢
    rw [fixedSpace_comm_t hR ρ g u, hu, map_neg]

theorem fixedSpace_exists_restrict {R : Subgroup K} {f : ℕ} {W : Type}
    [AddCommGroup W] [Module (ZMod f) W] (ρ : Representation (ZMod f) ↥R W)
    (U : Submodule (ZMod f) W) (hU : ∀ g : ↥R, ∀ u ∈ U, ρ g u ∈ U) :
    ∃ ρU : Representation (ZMod f) ↥R U, ∀ (g : ↥R) (u : U), ((ρU g u : U) : W) = ρ g u := by
  refine ⟨{ toFun := fun g => (ρ g).restrict (hU g), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext u
    simp
  · intro g h
    ext u
    simp
  · intro g u
    rfl

theorem exists_large_fixed_space {R : Subgroup K} {t : K} (hR : IsExt2 R t) {k : ℕ}
    (hk : Nat.card R = 2 ^ (1 + 2 * k)) (hk4 : 4 ≤ k) {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2)
    {W : Type} [AddCommGroup W] [Module (ZMod f) W] [Module.Finite (ZMod f) W]
    (ρ : Representation (ZMod f) ↥R W) (hnt : ∃ w : W, ρ ⟨t, hR.t_mem⟩ w ≠ w) :
    ∃ (y : K) (hy : y ∈ R), y ^ 2 = 1 ∧ y ∉ zpowers t ∧
      ∃ L : Submodule (ZMod f) W, 8 ≤ Module.finrank (ZMod f) L ∧
        ∀ w ∈ L, ρ ⟨y, hy⟩ w = w := by
  obtain ⟨U, hUnt, hUinv, hUt⟩ := fixedSpace_exists_sub hR ρ hnt
  obtain ⟨ρU, hρU⟩ := fixedSpace_exists_restrict ρ U hUinv
  have hρt : ∀ u : U, ρU ⟨t, hR.t_mem⟩ u = -u := by
    intro u
    apply Subtype.ext
    rw [hρU]
    exact hUt u u.2
  haveI : Nontrivial U := hUnt
  have hdim : 2 ^ k ≤ Module.finrank (ZMod f) U := ext2_module_dim hR hk hf2 ρU hρt
  obtain ⟨y, hy, hy2, hyt⟩ := IsExt2.exists_noncentral_involution hR hk (by omega)
  obtain ⟨r, hr, hyr⟩ := IsExt2.exists_swap hR hy hyt
  have hhalf := finrank_eq_two_mul_fixed hR hf2 ρU hρt hy hr hy2 hyr
  have h16 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
  refine ⟨y, hy, hy2, hyt,
    (Representation.invariants (ρU.comp (zpowers (⟨y, hy⟩ : ↥R)).subtype)).map U.subtype, ?_, ?_⟩
  · rw [Submodule.finrank_map_subtype_eq]
    omega
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := hw
    have h := (Representation.mem_invariants _ _).1 hu ⟨⟨y, hy⟩, mem_zpowers _⟩
    have h' : ρU ⟨y, hy⟩ u = u := h
    show ρ ⟨y, hy⟩ (u : W) = (u : W)
    rw [← hρU, h']
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem rankBound_zpow_cases {y : K} (hy2 : y ^ 2 = 1) (n : ℤ) : y ^ n = 1 ∨ y ^ n = y := by
  have h2 : y ^ (2 : ℤ) = 1 := by exact_mod_cast hy2
  have hn : y ^ n = (y ^ (2 : ℤ)) ^ (n / 2) * y ^ (n % 2) := by
    rw [← zpow_mul, ← zpow_add]
    congr 1
    omega
  rw [hn, h2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [h0, zpow_zero]
  · right
    rw [h1, zpow_one]

theorem rankBound_not_two_dvd {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) {M : Subgroup K}
    (hM : IsPGroup f M) : ¬ 2 ∣ Nat.card M := by
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  rw [hn]
  intro h
  have h' := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
  exact hf2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp h').symm

theorem rankBound_isPGroup_zpowers {y : K} (hy2 : y ^ 2 = 1) : IsPGroup 2 (zpowers y) := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨g, hg⟩ := g
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  apply Subtype.ext
  show (y ^ n) ^ (2 ^ 1) = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hy2]

theorem rankBound_fixed_lift {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) {M₀ : Subgroup K} {y : K}
    (hM₀ : IsPGroup f M₀) (hy2 : y ^ 2 = 1) (hyM : y ∈ normalizer (M₀ : Set K)) {x₀ : K}
    (hx : x₀⁻¹ * (y * x₀ * y⁻¹) ∈ M₀) : ∃ m ∈ M₀, y * (x₀ * m) = x₀ * m * y := by
  obtain ⟨m, hm, hfix⟩ := exists_fixed_in_coset (q := 2) (T := zpowers y) (M := M₀)
    (rankBound_isPGroup_zpowers hy2) (zpowers_le.mpr hyM) (rankBound_not_two_dvd hf2 hM₀) (x := x₀)
    (by
      intro s hs
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hs
      rcases rankBound_zpow_cases hy2 n with h1 | h1
      · rw [h1]
        simp
      · rw [h1]
        exact hx)
  refine ⟨m, hm, ?_⟩
  have := hfix y (mem_zpowers y)
  exact mul_inv_eq_iff_eq_mul.mp this

theorem rank_bound {p f : ℕ} {S X N : Subgroup K} {z : K} (h : Setup628 p f S X N z)
    (hrank : SmallRankInvolutionRankLE f 3 S X) {t : K} (hR : IsExt2 (RR S z) t) {k : ℕ}
    (hk : Nat.card (RR S z) = 2 ^ (1 + 2 * k)) : k ≤ 3 := by
  haveI : Fact f.Prime := ⟨h.hf⟩
  by_contra hk3
  have hRS : RR S z ≤ S := RR_le_S h.hzS
  obtain ⟨C, M₀, W, _, _, _, π, ρ, hCX, hM₀C, hCn, hM₀n, hcomm, hpow, hπadd, hπker, hπsurj,
    hπρ, hnt⟩ := exists_critical_section h hRS hR.t_mem hR.t_ne hR.t_sq
  obtain ⟨y, hy, hy2, hyt, L, hL8, hLfix⟩ :=
    exists_large_fixed_space hR hk (by omega) h.hf2 ρ hnt
  have hy1 : y ≠ 1 := fun h1 => hyt (h1 ▸ one_mem _)
  have hM₀X : IsPGroup f M₀ := h.hX.to_le (hM₀C.trans hCX)
  have hPC : C ⊓ centralizer ({y} : Set K) ≤ C := inf_le_left
  have hPX : C ⊓ centralizer ({y} : Set K) ≤ X := hPC.trans hCX
  have hfin := finrank_le_five h.hf2 (h.hX.to_le hPX)
    (fun x hx y' hy' w hw => hcomm x (hPC hx) y' (hPC hy') w (hPC hw))
    (fun x hx w hw => hpow x (hPC hx) w (hPC hw))
    ?_ π (fun x hx x' hx' => hπadd x (hPC hx) x' (hPC hx')) L ?_
  · omega
  · intro E hEP hEc hEexp
    refine card_le_pow_of_pRank_le h.hf (H := X ⊓ centralizer ({y} : Set K)) ?_ hEc hEexp
      (hrank y (hRS hy) hy2 hy1)
    intro a ha
    exact ⟨hPX (hEP ha), (hEP ha).2⟩
  · intro w hw
    obtain ⟨x₀, hx₀, rfl⟩ := hπsurj w
    have hyx : y * x₀ * y⁻¹ ∈ C := (mem_normalizer_iff.mp (hCn y hy) x₀).mp hx₀
    have hπy : π (y * x₀ * y⁻¹) = π x₀ := by
      have h1 : ρ ⟨y, hy⟩ (π x₀) = π (y * x₀ * y⁻¹) := hπρ ⟨y, hy⟩ x₀ hx₀
      rw [← h1]
      exact hLfix _ hw
    have hu : x₀⁻¹ * (y * x₀ * y⁻¹) ∈ C := mul_mem (inv_mem hx₀) hyx
    have hπu : π (x₀⁻¹ * (y * x₀ * y⁻¹)) = 0 := by
      have h0 : π x₀ + π (x₀⁻¹ * (y * x₀ * y⁻¹)) = π x₀ + 0 := by
        rw [add_zero, ← hπadd x₀ hx₀ _ hu, mul_inv_cancel_left, hπy]
      exact add_left_cancel h0
    have huM : x₀⁻¹ * (y * x₀ * y⁻¹) ∈ M₀ := (hπker _ hu).mp hπu
    obtain ⟨m, hm, hfix⟩ := rankBound_fixed_lift h.hf2 hM₀X hy2 (hM₀n y hy) huM
    refine ⟨x₀ * m, mem_inf.mpr ⟨mul_mem hx₀ (hM₀C hm), mem_centralizer_iff.mpr ?_⟩, ?_⟩
    · intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hfix
    · rw [hπadd x₀ hx₀ m (hM₀C hm), (hπker m (hM₀C hm)).mpr hm, add_zero]
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
