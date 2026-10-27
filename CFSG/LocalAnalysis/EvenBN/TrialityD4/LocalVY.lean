module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le isPGroup_oTwo le_normalizer_oTwo)
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem eq_one_of_mul_pow_eq_one_S {s j : X} (hs : s ∈ d.S) (hj : j ∈ d.J) {a : ℕ}
    (h : (s * j) ^ 2 ^ a = 1) : j = 1 := by
  have hpow : ∀ e : ℕ, ∃ s' ∈ d.S, (s * j) ^ e = s' * j ^ e := by
    intro e
    induction e with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ e ih =>
      obtain ⟨s', hs', he⟩ := ih
      have hjS : j ^ e ∈ normalizer (d.S : Set X) := pow_mem (d.J_le_normalizer_S hj) e
      refine ⟨s' * (j ^ e * s * (j ^ e)⁻¹), mul_mem hs' ((mem_normalizer_iff.1 hjS s).1 hs), ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨s', hs', he⟩ := hpow (2 ^ a)
  rw [h] at he
  have hjS : j ^ 2 ^ a ∈ d.S ⊓ d.J := by
    refine Subgroup.mem_inf.2 ⟨?_, pow_mem hj _⟩
    rw [eq_inv_of_mul_eq_one_right he.symm]
    exact inv_mem hs'
  rw [d.S_inf_J, mem_bot] at hjS
  obtain ⟨⟨l, m⟩, rfl⟩ := hj
  rw [← map_pow] at hjS
  have h1 := d.torus_injective (hjS.trans (map_one d.torus).symm)
  have hl : ((l : d.Γ₀) : d.Γ) ^ 2 ^ a = 1 ^ 2 ^ a := by
    have := congrArg (fun p => (((p.1 : (d.Γ₀)ˣ) : d.Γ₀) : d.Γ)) h1
    simpa using this
  have hm : ((m : d.Γˣ) : d.Γ) ^ 2 ^ a = 1 ^ 2 ^ a := by
    have := congrArg (fun p => ((p.2 : d.Γˣ) : d.Γ)) h1
    simpa using this
  have hl' : l = 1 := Units.ext (Subtype.ext (d.pow_two_pow_injective a hl))
  have hm' : m = 1 := Units.ext (d.pow_two_pow_injective a hm)
  rw [hl', hm']
  exact map_one d.torus

theorem φ_pow_mem_S (k : ℕ) {y : X} (hy : y ∈ d.S) : (d.φ ^ k) y ∈ d.S := by
  have h1 := map_rangeSubgroup_le_D4 d.x₁_add (d.φ ^ k) _ (d.φ_pow_x₁ k)
  have hD : d.D.map (d.φ ^ k).toMonoidHom ≤ d.D := by
    rintro _ ⟨z, hz, rfl⟩
    exact d.φ_pow_mem_D k hz
  have hS : d.S.map (d.φ ^ k).toMonoidHom ≤ d.S := by
    rw [d.S_eq_sup, Subgroup.map_sup]
    exact sup_le_sup h1 hD
  exact hS ⟨y, hy, rfl⟩

theorem mul_self_mem_M_of_mem_S {s : X} (hs : s ∈ d.S) : s * s ∈ d.M := by
  obtain ⟨a, m, hm, rfl⟩ := d.mem_S_iff_x₂.1 hs
  rw [show d.x₂ a * m * (d.x₂ a * m) = (d.x₂ a * m * (d.x₂ a)⁻¹) * (d.x₂ a * d.x₂ a) * m by
    group, d.x₂_mul_self, mul_one]
  exact mul_mem ((mem_normalizer_iff.1 (d.S_le_normalizer_M (d.U₂_le_S (d.x₂_mem_U₂ a))) m).1 hm)
    hm

end TrialityD4Data

section Mho

variable {G : Type*} [Group G]

@[expose] def mhoOne (P : Subgroup G) : Subgroup G :=
  closure {z | ∃ g ∈ P, g ^ 2 = z}

theorem sq_mem_mhoOne {P : Subgroup G} {g : G} (hg : g ∈ P) : g ^ 2 ∈ mhoOne P :=
  subset_closure ⟨g, hg, rfl⟩

theorem mhoOne_le {P K : Subgroup G} (h : ∀ g ∈ P, g ^ 2 ∈ K) : mhoOne P ≤ K := by
  rw [mhoOne, closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact h g hg

theorem conj_mem_mhoOne {P : Subgroup G} {n : G} (hn : n ∈ normalizer (P : Set G)) {x : G}
    (hx : x ∈ mhoOne P) : n * x * n⁻¹ ∈ mhoOne P := by
  have hle : mhoOne P ≤ (mhoOne P).comap (MulAut.conj n).toMonoidHom := by
    refine mhoOne_le fun g hg => ?_
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show n * g ^ 2 * n⁻¹ = (n * g * n⁻¹) ^ 2 by rw [sq, sq]; group]
    exact sq_mem_mhoOne ((mem_normalizer_iff.1 hn g).1 hg)
  have := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem le_normalizer_mhoOne (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (mhoOne P : Set G) := fun n hn => by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_mhoOne hn, fun hx => ?_⟩
  have := conj_mem_mhoOne (inv_mem hn) hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

end Mho

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section R₂

variable {q : ℕ}

omit [Finite G] in
theorem map_le_normalizer_map {E T : Subgroup L} (hT : T ≤ normalizer (E : Set L)) :
    T.map L.subtype ≤ normalizer ((E.map L.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨x * e * x⁻¹, (mem_normalizer_iff.1 (hT hx) e).1 he, rfl⟩
  · rintro ⟨e, he, hee⟩
    refine ⟨x⁻¹ * e * x, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 (hT (inv_mem hx)) e).1 he
      rwa [inv_inv] at this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hee ⊢
      rw [hee]
      group

theorem S_le_normalizer_tY (h : Setup G L f t) (d : TrialityD4Data L q) :
    d.S.map L.subtype ≤ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  fun _ hs => h.centralizer_inf_normalizer_Y_le d
    ⟨h.S_le_centralizer d hs, map_le_normalizer_map d.S_le_normalizer_Y hs⟩

theorem S_le_normalizer_tV (h : Setup G L f t) (d : TrialityD4Data L q) :
    d.S.map L.subtype ≤ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  fun _ hs => h.centralizer_inf_normalizer_V_le d
    ⟨h.S_le_centralizer d hs, map_le_normalizer_map d.S_le_normalizer_V hs⟩

theorem coe_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ((yamadaR₂ d t : Subgroup G) : Set G) =
      (yamadaL₂ d t : Set G) * ((d.S.map L.subtype : Subgroup G) : Set G) :=
  coe_mul_of_right_le_normalizer_left _ _
    ((h.S_le_normalizer_tY d).trans (le_normalizer_yamadaL₂ d t))

theorem tM_le_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    d.M.map L.subtype ⊔ zpowers t ≤ yamadaL₂ d t := by
  rw [← (h.two_core_L₂ d).2.1]
  exact inf_le_left

theorem tD_le_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    d.D.map L.subtype ⊔ zpowers t ≤ yamadaC₁ d t := by
  rw [← (h.two_core_C₁_all d).2.1]
  exact inf_le_left

theorem yamadaR₂_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR₂ d t ⊓ centralizer ({t} : Set G) = yamadaR d t := by
  have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
  have hMS : d.M.map L.subtype ≤ d.S.map L.subtype := map_mono d.M_le_S
  apply le_antisymm
  · intro z hz
    obtain ⟨hz, hzC⟩ := Subgroup.mem_inf.1 hz
    have hz' : z ∈ ((yamadaR₂ d t : Subgroup G) : Set G) := hz
    rw [h.coe_yamadaR₂ d] at hz'
    obtain ⟨l, hl, s, hs, rfl⟩ := hz'
    have hsC := h.S_le_centralizer d hs
    have hlC : l ∈ centralizer ({t} : Set G) := by
      have := mul_mem hzC (inv_mem hsC)
      rwa [mul_inv_cancel_right] at this
    have hlM : l ∈ d.M.map L.subtype ⊔ zpowers t := by
      rw [← (h.two_core_L₂ d).2.1]
      exact ⟨hl, hlC⟩
    rw [hR]
    exact mul_mem (sup_le_sup_right hMS _ hlM) (mem_sup_left hs)
  · rw [hR]
    refine le_inf (sup_le le_sup_right ((zpowers_le).2 ?_)) (h.yamadaR_le_centralizer d |>.trans'
      (le_of_eq hR.symm))
    exact mem_sup_left (h.tM_le_yamadaL₂ d (mem_sup_right (mem_zpowers t)))

theorem normalizer_yamadaR_le_normalizer_yamadaR₂ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) :
    normalizer (yamadaR d t : Set G) ≤ normalizer (yamadaR₂ d t : Set G) := fun _ hn =>
  mem_normalizer_sup (le_normalizer_yamadaL₂ d t (h.normalizer_yamadaR_le_tY d hn))
    ((h.yamada_5_3_3_all d).2.2 hn)

theorem yamadaR₁_le_normalizer_yamadaR (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR₁ d t ≤ normalizer (yamadaR d t : Set G) := by
  refine sup_le (h.yamadaC₁_le_normalizer_yamadaR_of_core d (h.two_core_C₁_all d)) ?_
  intro s hs
  rw [yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)]
  exact mem_normalizer_sup (le_normalizer hs)
    (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)))

theorem exists_mul_of_mem_normalizer_yamadaR (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {x : G} (hx : x ∈ normalizer (yamadaR d t : Set G)) :
    ∃ c ∈ centralizer ({t} : Set G) ⊓ normalizer (yamadaR d t : Set G), ∃ l ∈ yamadaL₂ d t,
      x = c * l := by
  obtain ⟨c, hc, l, hl, rfl⟩ := (h.two_core_L₂ d).2.2.2 x (h.normalizer_yamadaR_le_tY d hx)
  have hlR₂ : l ∈ yamadaR₂ d t := mem_sup_left hl
  have hcR₂ : c ∈ normalizer (yamadaR₂ d t : Set G) := by
    have := mul_mem (h.normalizer_yamadaR_le_normalizer_yamadaR₂ d hx)
      (inv_mem (le_normalizer hlR₂))
    rwa [mul_inv_cancel_right] at this
  refine ⟨c, ⟨hc.1, ?_⟩, l, hl, rfl⟩
  rw [← h.yamadaR₂_inf_centralizer d]
  exact Common.mem_normalizer_inf hcR₂ (le_normalizer hc.1)

end R₂

section R₁

theorem mem_yamadaR_of_act_eq_conj (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {z : G}
    (hz : z ∈ centralizer ({t} : Set G)) {g : L} (hg : g ∈ d.B)
    (hzg : h.act ⟨z, hz⟩ = MulAut.conj g) {a : ℕ} (ha : z ^ 2 ^ a = 1) : z ∈ yamadaR d t := by
  obtain ⟨c, hc, rfl⟩ := h.exists_mul_zpowers_of_act_eq_conj d hz hzg
  obtain ⟨s, hs, j, hj, rfl⟩ := d.mem_B_iff.1 hg
  have hc2 : c * c = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
    · exact mul_one 1
    · exact h.t_mul_t
  have hcomm : Commute ((s * j : L) : G) c := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    exact Commute.zpow_right (mem_centralizer_iff.1 h.htL _ (s * j).2) k
  have hsj : (s * j) ^ 2 ^ (a + 1) = 1 := by
    have h2 : ((s * j : L) : G) ^ 2 ^ (a + 1) * c ^ 2 ^ (a + 1) = 1 := by
      rw [← hcomm.mul_pow, pow_succ, pow_mul, ha, one_pow]
    have hc' : c ^ 2 ^ (a + 1) = 1 := by rw [pow_succ', pow_mul, sq, hc2, one_pow]
    rw [hc', mul_one] at h2
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow, h2, OneMemClass.coe_one])
  rw [d.eq_one_of_mul_pow_eq_one_S hs hj hsj, mul_one,
    yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)]
  exact mul_mem (mem_sup_left ⟨s, hs, rfl⟩) (mem_sup_right hc)

theorem isPGroup_yamadaR₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    IsPGroup 2 (yamadaR₁ d t : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 (d.S.map L.subtype : Subgroup G) := by
    obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
    exact (hP ▸ P.isPGroup').map _
  exact (LieType.BorelTits.pCoreOf_isPGroup 2 _).to_sup_of_normal_left' hS
    ((h.S_le_normalizer_tV d).trans (le_normalizer_yamadaC₁ d t))

theorem isPGroup_yamadaR₁_sup_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    IsPGroup 2 (yamadaR₁ d t ⊔ yamadaL₂ d t : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (h.isPGroup_yamadaR₁ d).to_sup_of_normal_right' (LieType.BorelTits.pCoreOf_isPGroup 2 _)
    ((h.yamadaR₁_le_normalizer_yamadaR d).trans
      ((h.normalizer_yamadaR_le_tY d).trans (le_normalizer_yamadaL₂ d t)))

theorem yamadaR_le_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR d t ≤ yamadaR₂ d t := by
  rw [← h.yamadaR₂_inf_centralizer d]
  exact inf_le_left

theorem exists_B_of_mem_normalizer_yamadaR (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {c : G} (hc : c ∈ centralizer ({t} : Set G) ⊓ normalizer (yamadaR d t : Set G)) :
    ∃ g ∈ d.B, ∃ k : ℕ, h.act ⟨c, hc.1⟩ = MulAut.conj g * d.φ ^ k := by
  obtain ⟨g, k, hgk⟩ := d.aut_eq (h.act ⟨c, hc.1⟩)
  refine ⟨g, ?_, k, hgk⟩
  have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
  have hcS : ∀ s ∈ d.S, (MulAut.conj g * d.φ ^ k) s ∈ d.S := by
    intro s hs
    rw [← hgk]
    have h1 : c * (s : G) * c⁻¹ ∈ yamadaR d t ⊓ L :=
      ⟨(mem_normalizer_iff.1 hc.2 _).1 (hR ▸ mem_sup_left ⟨s, hs, rfl⟩),
        (mem_normalizer_iff.1 (h.centralizer_le_normalizer hc.1) _).1 s.2⟩
    rw [h.yamadaR_inf_L d] at h1
    rw [← h.conj_mem_map_iff hc.1]
    exact h1
  have := d.finite
  rw [← d.normalizer_S]
  refine mem_normalizer_fintype fun s hs => ?_
  have hsurj : Function.Surjective fun s₀ : d.S => (⟨(d.φ ^ k) s₀, d.φ_pow_mem_S k s₀.2⟩ : d.S) :=
    Finite.surjective_of_injective fun a b hab => Subtype.ext ((d.φ ^ k).injective
      (congrArg Subtype.val hab))
  obtain ⟨s₀, hs₀⟩ := hsurj ⟨s, hs⟩
  have h1 := hcS s₀ s₀.2
  rw [MulAut.mul_apply, MulAut.conj_apply] at h1
  have h2 : (d.φ ^ k) s₀ = s := congrArg Subtype.val hs₀
  rwa [h2] at h1

end R₁

section R₁Main

theorem yamadaC₁_le_yamadaR₂_of_odd (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : Odd f) : yamadaC₁ d t ≤ yamadaR₂ d t := by
  intro x hx
  have hxN := h.yamadaR₁_le_normalizer_yamadaR d (mem_sup_left hx)
  obtain ⟨c, hc, l, hl, rfl⟩ := h.exists_mul_of_mem_normalizer_yamadaR d hxN
  have hP := h.isPGroup_yamadaR₁_sup_yamadaL₂ d
  have hcP : c ∈ yamadaR₁ d t ⊔ yamadaL₂ d t := by
    have := mul_mem (mem_sup_left (mem_sup_left hx) : c * l ∈ yamadaR₁ d t ⊔ yamadaL₂ d t)
      (inv_mem (mem_sup_right hl))
    rwa [mul_inv_cancel_right] at this
  have hcL : c ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :=
    h.le_sup_kernel_of_isPGroup d hf (hP.to_le ((zpowers_le).2 hcP))
      ((zpowers_le).2 hc.1) (mem_zpowers c)
  obtain ⟨g, hg⟩ := (h.act_mem_range_conj_iff ⟨c, hc.1⟩).2 hcL
  have hgB : g ∈ d.B := by
    have := d.finite
    rw [← d.normalizer_S]
    refine mem_normalizer_fintype fun s hs => ?_
    have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
    have h1 : c * (s : G) * c⁻¹ ∈ yamadaR d t ⊓ L :=
      ⟨(mem_normalizer_iff.1 hc.2 _).1 (hR ▸ mem_sup_left ⟨s, hs, rfl⟩),
        (mem_normalizer_iff.1 (h.centralizer_le_normalizer hc.1) _).1 s.2⟩
    rw [h.yamadaR_inf_L d, ← h.coe_act_apply ⟨c, hc.1⟩ s, ← hg, MulAut.conj_apply] at h1
    exact coe_mem_map_subtype_iff_D4.1 h1
  obtain ⟨a, ha⟩ := hP ⟨c, hcP⟩
  have ha' : c ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hcR := h.mem_yamadaR_of_act_eq_conj d hc.1 hgB hg.symm ha'
  exact mul_mem (h.yamadaR_le_yamadaR₂ d hcR) (mem_sup_left hl)

theorem yamadaC₁_le_yamadaR₂_of_four_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hq : 4 ≤ 2 ^ f) : yamadaC₁ d t ≤ yamadaR₂ d t := by
  obtain ⟨hC₁V, hC₁C, hC₁tr, -⟩ := h.two_core_C₁_all d
  have hc := h.cosetData_tV d
  have hC₁H := yamadaC₁_le d t
  have hC₁K : ∀ {x}, x ∈ yamadaC₁ d t → x ∈
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ((d.V.map L.subtype : Subgroup G) : Set G) := fun hx => ⟨hC₁H hx, hC₁V hx⟩
  have hJ₁ : ∀ l : (d.Γ₀)ˣ, ((d.torus (l, 1) : L) : G) ∈ centralizer ({t} : Set G) ⊓
      normalizer (yamadaR d t : Set G) ∧
      ((d.torus (l, 1) : L) : G) ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) :
        Set G) := by
    intro l
    have hj : d.torus (l, 1) ∈ d.J := d.torus_mem_J _
    have hjC := h.L_le_centralizer (d.torus (l, 1)).2
    have hjS : ((d.torus (l, 1) : L) : G) ∈ centralizer ({t} : Set G) ⊓
        normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
      ⟨hjC, map_le_normalizer_map d.J_le_normalizer_S ⟨_, hj, rfl⟩⟩
    have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
    refine ⟨⟨hjC, ?_⟩, h.centralizer_inf_normalizer_V_le d
      ⟨hjC, map_le_normalizer_map d.J_le_normalizer_V ⟨_, hj, rfl⟩⟩⟩
    rw [hR]
    exact mem_normalizer_sup hjS.2
      (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 hjC))
  have hjx₆ : ∀ (l : (d.Γ₀)ˣ) (b : d.Γ₀), ((d.torus (l, 1) : L) : G) * ((d.x₆ b : L) : G) *
      ((d.torus (l, 1) : L) : G)⁻¹ = ((d.x₆ ((l : d.Γ₀) * (l : d.Γ₀) * b) : L) : G) := by
    intro l b
    rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      d.torus_conj_x₆_of_snd_eq_one]
  have hκV : ∀ {x}, x ∈ yamadaC₁ d t → x⁻¹ * t * x * t ∈ d.V.map L.subtype := fun hx =>
    hc.crossed_mem_of_mem (hC₁K hx)
  obtain ⟨lam, hlam⟩ := d.exists_units₀_ne_one hq
  have hlam2 : (lam : d.Γ₀) * (lam : d.Γ₀) ≠ 1 := by
    intro h1
    exact hlam (d.units₀_eq_one_of_sq (Units.ext (by rw [Units.val_pow_eq_pow_val, sq, h1,
      Units.val_one])))
  set j : G := ((d.torus (lam, 1) : L) : G) with hjdef
  obtain ⟨⟨hjC, hjR⟩, hjH⟩ := hJ₁ lam
  obtain ⟨x, hx, hxt⟩ := hC₁tr _ (⟨_, d.x₆_mem_V 1, rfl⟩ : ((d.x₆ 1 : L) : G) ∈
    d.V.map L.subtype)
  have hκx : x⁻¹ * t * x * t = ((d.x₆ 1 : L) : G) := by
    rw [hxt, mul_assoc, mem_centralizer_iff.1 h.htL _ (d.x₆ 1).2, ← mul_assoc, h.t_mul_t,
      one_mul]
  set w := x * j * x⁻¹ * j⁻¹ with hwdef
  have hjx : j * x⁻¹ * j⁻¹ ∈ yamadaC₁ d t :=
    (mem_normalizer_iff.1 (le_normalizer_yamadaC₁ d t hjH) _).1 (inv_mem hx)
  have hwC₁ : w ∈ yamadaC₁ d t := by
    rw [hwdef, show x * j * x⁻¹ * j⁻¹ = x * (j * x⁻¹ * j⁻¹) by group]
    exact mul_mem hx hjx
  have hκw : w⁻¹ * t * w * t =
      ((d.x₆ (1 + (lam : d.Γ₀) * (lam : d.Γ₀)) : L) : G) := by
    rw [hwdef, show x * j * x⁻¹ * j⁻¹ = x * (j * x⁻¹ * j⁻¹) by group,
      hc.crossed_mul_of_mem (hC₁K hx) (hC₁K hjx),
      CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (mem_centralizer_singleton_iff.1 hjC),
      hc.crossed_inv_of_mem (hC₁K hx), hκx, ← Subgroup.coe_inv (x := d.x₆ 1), d.x₆_inv,
      hjx₆, ← Subgroup.coe_mul, ← d.x₆_add, mul_one]
  have hwR₂ : w ∈ yamadaR₂ d t := by
    obtain ⟨c, hc', l, hl, rfl⟩ := h.exists_mul_of_mem_normalizer_yamadaR d
      (h.yamadaR₁_le_normalizer_yamadaR d (mem_sup_left hx))
    have hcY := h.normalizer_yamadaR_le_tY d hc'.2
    have hjY : j ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
      h.normalizer_yamadaR_le_tY d hjR
    have hl' : c * (l * j * l⁻¹ * j⁻¹) * c⁻¹ ∈ yamadaL₂ d t := by
      refine (mem_normalizer_iff.1 (le_normalizer_yamadaL₂ d t hcY) _).1 ?_
      rw [show l * j * l⁻¹ * j⁻¹ = l * (j * l⁻¹ * j⁻¹) by group]
      exact mul_mem hl ((mem_normalizer_iff.1 (le_normalizer_yamadaL₂ d t hjY) _).1 (inv_mem hl))
    have e1 : w = (c * (l * j * l⁻¹ * j⁻¹) * c⁻¹) * (c * j * c⁻¹ * j⁻¹) := by
      rw [hwdef]
      group
    have hcj : c * j * c⁻¹ * j⁻¹ ∈ yamadaR d t := by
      have hcjC : c * j * c⁻¹ * j⁻¹ ∈ centralizer ({t} : Set G) :=
        mul_mem (mul_mem (mul_mem hc'.1 hjC) (inv_mem hc'.1)) (inv_mem hjC)
      have hP := h.isPGroup_yamadaR₁_sup_yamadaL₂ d
      have hcjP : c * j * c⁻¹ * j⁻¹ ∈ yamadaR₁ d t ⊔ yamadaL₂ d t := by
        have e2 : c * j * c⁻¹ * j⁻¹ = (c * (l * j * l⁻¹ * j⁻¹) * c⁻¹)⁻¹ * w := by
          rw [e1]
          group
        rw [e2]
        exact mul_mem (inv_mem (mem_sup_right hl')) (mem_sup_left (mem_sup_left hwC₁))
      obtain ⟨a, ha⟩ := hP ⟨_, hcjP⟩
      have ha' : (c * j * c⁻¹ * j⁻¹) ^ 2 ^ a = 1 := by
        have := congrArg Subtype.val ha
        simpa using this
      obtain ⟨g, hg, k, hgk⟩ := h.exists_B_of_mem_normalizer_yamadaR d hc'
      have hact : h.act ⟨c * j * c⁻¹ * j⁻¹, hcjC⟩ = MulAut.conj
          (g * (d.φ ^ k) (d.torus (lam, 1)) * g⁻¹ * (d.torus (lam, 1))⁻¹) := by
        have e3 : (⟨c * j * c⁻¹ * j⁻¹, hcjC⟩ : centralizer ({t} : Set G)) =
            ⟨c, hc'.1⟩ * ⟨j, hjC⟩ * ⟨c, hc'.1⟩⁻¹ * ⟨j, hjC⟩⁻¹ := rfl
        have e2 : ∀ β : MulAut L, β * MulAut.conj (d.torus (lam, 1)) * β⁻¹ *
            (MulAut.conj (d.torus (lam, 1)))⁻¹ =
              MulAut.conj (β (d.torus (lam, 1)) * (d.torus (lam, 1))⁻¹) := by
          intro β
          rw [mulAut_mul_conj_mul_inv, map_mul, map_inv]
        rw [e3, map_mul, map_mul, map_mul, map_inv, map_inv, hgk,
          show (⟨j, hjC⟩ : centralizer ({t} : Set G)) =
            ⟨_, h.L_le_centralizer (d.torus (lam, 1)).2⟩ from rfl,
          h.act_of_mem_L (d.torus (lam, 1)).2, Subtype.coe_eta, e2, MulAut.mul_apply,
          MulAut.conj_apply]
      have hgB : g * (d.φ ^ k) (d.torus (lam, 1)) * g⁻¹ * (d.torus (lam, 1))⁻¹ ∈ d.B := by
        have hφB : (d.φ ^ k) (d.torus (lam, 1)) ∈ d.B := by
          rw [d.φ_pow_torus]
          exact d.J_le_B (d.torus_mem_J _)
        exact mul_mem (mul_mem (mul_mem hg hφB) (inv_mem hg))
          (inv_mem (d.J_le_B (d.torus_mem_J _)))
      exact h.mem_yamadaR_of_act_eq_conj d hcjC hgB hact ha'
    rw [e1]
    exact mul_mem (mem_sup_left hl') (h.yamadaR_le_yamadaR₂ d hcj)
  have hκall : ∀ b : d.Γ₀, ∃ z ∈ yamadaC₁ d t ⊓ yamadaR₂ d t,
      z⁻¹ * t * z * t = ((d.x₆ b : L) : G) := by
    intro b
    by_cases hb : b = 0
    · refine ⟨1, one_mem _, ?_⟩
      rw [hb, d.x₆_zero, inv_one, one_mul, mul_one, h.t_mul_t]
      rfl
    set b₀ := 1 + (lam : d.Γ₀) * (lam : d.Γ₀) with hb₀
    have hb₀0 : b₀ ≠ 0 := by
      intro h0
      apply hlam2
      have := congrArg (· + 1) h0
      simp only [hb₀] at this
      rw [show 1 + (lam : d.Γ₀) * (lam : d.Γ₀) + 1 = (lam : d.Γ₀) * (lam : d.Γ₀) + (1 + 1) by
        ring, d.add_self_Γ₀, add_zero, zero_add] at this
      exact this
    obtain ⟨l', hl'⟩ := d.sq_surjective_units₀ (Units.mk0 (b / b₀) (div_ne_zero hb hb₀0))
    obtain ⟨⟨-, hj'R⟩, hj'H⟩ := hJ₁ l'
    set j' : G := ((d.torus (l', 1) : L) : G)
    have hj'C := h.L_le_centralizer (d.torus (l', 1)).2
    refine ⟨j' * w * j'⁻¹, ⟨(mem_normalizer_iff.1 (le_normalizer_yamadaC₁ d t hj'H) w).1 hwC₁,
      (mem_normalizer_iff.1 (h.normalizer_yamadaR_le_normalizer_yamadaR₂ d hj'R) w).1 hwR₂⟩, ?_⟩
    rw [CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (mem_centralizer_singleton_iff.1 hj'C),
      hκw, hjx₆]
    congr 2
    have hl'v : (l' : d.Γ₀) * (l' : d.Γ₀) = b / b₀ := by
      rw [← sq, ← Units.val_pow_eq_pow_val, hl', Units.val_mk0]
    rw [hl'v, div_mul_cancel₀ b hb₀0]
  intro y hy
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hκV hy
  simp only [Subgroup.coe_subtype] at hb
  obtain ⟨z, ⟨hzC₁, hzR₂⟩, hzκ⟩ := hκall b
  have h1 : (y * z⁻¹)⁻¹ * t * (y * z⁻¹) * t = 1 := by
    rw [hc.crossed_mul_of_mem (hC₁K hy) (hC₁K (inv_mem hzC₁)), hc.crossed_inv_of_mem (hC₁K hzC₁),
      ← hb, hzκ, mul_inv_cancel]
  have h2 : y * z⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h3 : (y * z⁻¹)⁻¹ * t * (y * z⁻¹) = t := by
      calc (y * z⁻¹)⁻¹ * t * (y * z⁻¹) = (y * z⁻¹)⁻¹ * t * (y * z⁻¹) * t * t := by
            rw [mul_assoc _ t t, h.t_mul_t, mul_one]
        _ = t := by rw [h1, one_mul]
    calc y * z⁻¹ * t = y * z⁻¹ * ((y * z⁻¹)⁻¹ * t * (y * z⁻¹)) := by rw [h3]
      _ = t * (y * z⁻¹) := by group
  have h4 : y * z⁻¹ ∈ d.D.map L.subtype ⊔ zpowers t := by
    rw [← hC₁C]
    exact Subgroup.mem_inf.2 ⟨mul_mem hy (inv_mem hzC₁), h2⟩
  have h5 : y * z⁻¹ ∈ yamadaR₂ d t := by
    refine h.yamadaR_le_yamadaR₂ d ?_
    rw [yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)]
    exact sup_le_sup_right (map_mono d.D_le_S) _ h4
  rw [show y = y * z⁻¹ * z by group]
  exact mul_mem h5 hzR₂

theorem yamadaC₁_le_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaC₁ d t ≤ yamadaR₂ d t := by
  rcases Nat.lt_or_ge f 2 with hf | hf
  · have hf1 : f = 1 := by have := h.one_le; omega
    exact h.yamadaC₁_le_yamadaR₂_of_odd d (by rw [hf1]; exact odd_one)
  · exact h.yamadaC₁_le_yamadaR₂_of_four_le d (by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)

end R₁Main

section Quotient

variable {q : ℕ}

omit [Finite G] in
instance normal_V_subgroupOf_Y (d : TrialityD4Data L q) :
    ((d.V.map L.subtype).subgroupOf (d.Y.map L.subtype)).Normal := by
  have hY := isElementaryAbelian_Y_map (G := G) d
  have : IsMulCommutative (d.Y.map L.subtype : Subgroup G) := hY.toIsMulCommutative
  exact Subgroup.normal_of_isMulCommutative _

omit [Finite G] in
theorem crossed_mul_general {t z z' : G} (ht : t * t = 1) :
    (z * z')⁻¹ * t * (z * z') * t = z'⁻¹ * (z⁻¹ * t * z * t) * z' * (z'⁻¹ * t * z' * t) := by
  calc (z * z')⁻¹ * t * (z * z') * t = z'⁻¹ * z⁻¹ * t * z * (t * t) * z' * t := by rw [ht]; group
    _ = _ := by group

theorem yamadaR₂_le_normalizer_tY (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR₂ d t ≤ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
  sup_le (yamadaL₂_le d t) (h.S_le_normalizer_tY d)

theorem crossed_mem_Y_of_mem_yamadaR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {z : G} (hz : z ∈ yamadaR₂ d t) : z⁻¹ * t * z * t ∈ d.Y.map L.subtype :=
  (h.cosetData_tY d).crossed_mem z (h.yamadaR₂_le_normalizer_tY d hz)

theorem t_crossed_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {z : G}
    (hz : z ∈ yamadaR₂ d t) : t * z⁻¹ * t * z = z⁻¹ * t * z * t := by
  have hY := h.crossed_mem_Y_of_mem_yamadaR₂ d hz
  have htY : t * (z⁻¹ * t * z * t) = (z⁻¹ * t * z * t) * t := (h.cosetData_tY d).comm_of_mem hY
  calc t * z⁻¹ * t * z = t * (z⁻¹ * t * z * t) * t := by
        rw [show t * (z⁻¹ * t * z * t) * t = t * z⁻¹ * t * z * (t * t) by group, h.t_mul_t,
          mul_one]
    _ = (z⁻¹ * t * z * t) * (t * t) := by rw [htY, mul_assoc]
    _ = z⁻¹ * t * z * t := by rw [h.t_mul_t, mul_one]

theorem t_crossed_mem_Y (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {z : G}
    (hz : z ∈ yamadaR₂ d t) : t * z⁻¹ * t * z ∈ d.Y.map L.subtype := by
  rw [h.t_crossed_eq d hz]
  exact h.crossed_mem_Y_of_mem_yamadaR₂ d hz

theorem conj_mem_Y_mod_V (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {z : G}
    (hz : z ∈ yamadaR₂ d t) {y : G} (hy : y ∈ d.Y.map L.subtype) :
    z⁻¹ * y * z * y⁻¹ ∈ d.V.map L.subtype := by
  have hz' : z ∈ ((yamadaR₂ d t : Subgroup G) : Set G) := hz
  rw [h.coe_yamadaR₂ d] at hz'
  obtain ⟨l, hl, s, hs, rfl⟩ := hz'
  have hly : l⁻¹ * y * l = y := by
    rw [mul_assoc, mem_centralizer_iff.1 ((h.two_core_L₂ d).1 hl) y hy, inv_mul_cancel_left]
  rw [show (l * s)⁻¹ * y * (l * s) * y⁻¹ = s⁻¹ * (l⁻¹ * y * l) * s * y⁻¹ by group, hly]
  obtain ⟨s₀, hs₀, rfl⟩ := hs
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  refine ⟨s₀⁻¹ * y₀ * s₀ * y₀⁻¹, ?_, by simp⟩
  have := d.commutator_S_Y (commutator_mem_commutator (inv_mem hs₀) hy₀)
  rwa [commutatorElement_def, inv_inv] at this

@[expose] noncomputable def psiR₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR₂ d t →* (d.Y.map L.subtype : Subgroup G) ⧸
      (d.V.map L.subtype).subgroupOf (d.Y.map L.subtype) where
  toFun z := QuotientGroup.mk ⟨t * (z : G)⁻¹ * t * z, h.t_crossed_mem_Y d z.2⟩
  map_one' := by
    refine (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 ?_)
    change t * (1 : G)⁻¹ * t * 1 ∈ d.V.map L.subtype
    rw [inv_one, mul_one, mul_one, h.t_mul_t]
    exact one_mem _
  map_mul' a b := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    simp only [Subgroup.coe_inv, MulMemClass.coe_mul]
    rw [h.t_crossed_eq d a.2, h.t_crossed_eq d b.2, h.t_crossed_eq d (mul_mem a.2 b.2),
      crossed_mul_general h.t_mul_t]
    have h1 := h.conj_mem_Y_mod_V d b.2 (h.crossed_mem_Y_of_mem_yamadaR₂ d a.2)
    have hYc := isElementaryAbelian_Y_map (G := G) d
    have hcomm : ∀ x ∈ d.Y.map L.subtype, ∀ y ∈ d.Y.map L.subtype, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hYc.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    set A := (a : G)⁻¹ * t * a * t
    set B := (b : G)⁻¹ * t * b * t
    have hA : A ∈ d.Y.map L.subtype := h.crossed_mem_Y_of_mem_yamadaR₂ d a.2
    have hB : B ∈ d.Y.map L.subtype := h.crossed_mem_Y_of_mem_yamadaR₂ d b.2
    have hbA : (b : G)⁻¹ * A * b ∈ d.Y.map L.subtype := by
      have := mul_mem (map_mono d.V_le_Y h1) hA
      rwa [inv_mul_cancel_right] at this
    have key : ((b : G)⁻¹ * A * b * B)⁻¹ * (A * B) = ((b : G)⁻¹ * A * b * A⁻¹)⁻¹ := by
      have e1 : ((b : G)⁻¹ * A * b * B)⁻¹ * (A * B) = B⁻¹ * (((b : G)⁻¹ * A * b)⁻¹ * A) * B := by
        group
      rw [e1, mul_assoc, hcomm _ (mul_mem (inv_mem hbA) hA) _ hB, inv_mul_cancel_left,
        hcomm _ (inv_mem hbA) _ hA]
      group
    rw [key]
    exact inv_mem h1

theorem centralizer_inf_normalizer_S_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR d t : Set G) := by
  intro c hc
  rw [yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)]
  exact mem_normalizer_sup hc.2 (mem_normalizer_zpowers_of_comm_D4
    (mem_centralizer_singleton_iff.1 hc.1))

end Quotient

section Estar

omit [Finite G] in
theorem crossed_commutator_sq_eq_one {H Y : Subgroup G} (hc : CosetData H Y t) {a b : G}
    (ha : a ∈ H ⊓ centralizer (Y : Set G)) (hb : b ∈ H ⊓ centralizer (Y : Set G)) :
    (a * b * a⁻¹ * b⁻¹)⁻¹ * t * (a * b * a⁻¹ * b⁻¹) * t = 1 ∧
      (a * a)⁻¹ * t * (a * a) * t = 1 := by
  constructor
  · rw [hc.crossed_mul_of_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb),
      hc.crossed_conj_of_mem ha hb, hc.crossed_inv_of_mem hb, mul_inv_cancel]
  · rw [hc.crossed_mul_of_mem ha ha, hc.mul_self_of_mem (hc.crossed_mem_of_mem ha)]

theorem crossed_eq_one_iff_D4 (h : Setup G L f t) {z : G} :
    z⁻¹ * t * z * t = 1 ↔ z ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_eq_one_iff h.t_mul_t

theorem commutator_sq_mem_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {a b : G} (ha : a ∈ yamadaR₂ d t) (hb : b ∈ yamadaR₂ d t) :
    a * b * a⁻¹ * b⁻¹ ∈ yamadaL₂ d t ∧ a * a ∈ yamadaL₂ d t := by
  have hSL₂ := (h.S_le_normalizer_tY d).trans (le_normalizer_yamadaL₂ d t)
  have hML₂ : d.M.map L.subtype ≤ yamadaL₂ d t := le_sup_left.trans (h.tM_le_yamadaL₂ d)
  have ha' : a ∈ ((yamadaR₂ d t : Subgroup G) : Set G) := ha
  have hb' : b ∈ ((yamadaR₂ d t : Subgroup G) : Set G) := hb
  rw [h.coe_yamadaR₂ d] at ha' hb'
  obtain ⟨l, hl, s, hs, rfl⟩ := ha'
  obtain ⟨l', hl', s', hs', rfl⟩ := hb'
  have hconj : ∀ {x m : G}, x ∈ d.S.map L.subtype → m ∈ yamadaL₂ d t →
      x * m * x⁻¹ ∈ yamadaL₂ d t := fun hx hm => (mem_normalizer_iff.1 (hSL₂ hx) _).1 hm
  constructor
  · have hss : s * s' * s⁻¹ * s'⁻¹ ∈ yamadaL₂ d t := by
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      obtain ⟨s₀', hs₀', rfl⟩ := hs'
      refine hML₂ ⟨s₀ * s₀' * s₀⁻¹ * s₀'⁻¹, d.F_le_M (d.commutator_S_S ?_), by simp⟩
      rw [← commutatorElement_def]
      exact commutator_mem_commutator hs₀ hs₀'
    rw [show l * s * (l' * s') * (l * s)⁻¹ * (l' * s')⁻¹ =
      l * (s * l' * s⁻¹) * (s * s' * s⁻¹ * s'⁻¹) * (s' * l⁻¹ * s'⁻¹) * l'⁻¹ by group]
    exact mul_mem (mul_mem (mul_mem (mul_mem hl (hconj hs hl')) hss) (hconj hs' (inv_mem hl)))
      (inv_mem hl')
  · have hs2 : s * s ∈ yamadaL₂ d t := by
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      exact hML₂ ⟨s₀ * s₀, d.mul_self_mem_M_of_mem_S hs₀, by simp⟩
    rw [show l * s * (l * s) = l * (s * l * s⁻¹) * (s * s) by group]
    exact mul_mem (mul_mem hl (hconj hs hl)) hs2

theorem x₂_one_not_mem_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ((d.x₂ 1 : L) : G) ∉ yamadaL₂ d t := by
  intro hx
  have hS : ((d.x₂ 1 : L) : G) ∈ d.S.map L.subtype := ⟨_, d.U₂_le_S (d.x₂_mem_U₂ 1), rfl⟩
  have h1 : ((d.x₂ 1 : L) : G) ∈ d.M.map L.subtype ⊔ zpowers t := by
    rw [← (h.two_core_L₂ d).2.1]
    exact Subgroup.mem_inf.2 ⟨hx, h.S_le_centralizer d hS⟩
  rcases (h.mem_sup_zpowers_iff (map_subtype_le d.M)).1 h1 with h2 | h2
  · exact one_ne_zero (d.x₂_mem_M_iff.1 (coe_mem_map_subtype_iff_D4.1 h2))
  · apply h.t_not_mem_L
    have := mul_mem (map_subtype_le _ h2) (inv_mem (d.x₂ 1).2)
    rwa [mul_inv_cancel_right] at this

end Estar

section Mho

omit [Finite G] in
theorem mem_normalizer_comap_subtype {K : Subgroup G} {l : L}
    (hl : (l : G) ∈ normalizer (K : Set G)) :
    l ∈ normalizer ((K.comap L.subtype : Subgroup L) : Set L) := by
  rw [mem_normalizer_iff]
  intro y
  exact mem_normalizer_iff.1 hl y

theorem sq_ne_t_mul_of_mem_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {g : G}
    (hg : g ∈ yamadaC₁ d t) {v : G} (hv : v ∈ d.V.map L.subtype) : g ^ 2 ≠ t * v := by
  intro he
  obtain ⟨-, hC₁C, hC₁tr, -⟩ := h.two_core_C₁_all d
  obtain ⟨c, hc, hct⟩ := hC₁tr v hv
  obtain ⟨y, hydef⟩ : ∃ y, y = c * g * c⁻¹ := ⟨_, rfl⟩
  have hy : y ∈ yamadaC₁ d t := by
    rw [hydef]
    exact mul_mem (mul_mem hc hg) (inv_mem hc)
  have hy2 : y * y = t := by
    calc y * y = c * g ^ 2 * c⁻¹ := by rw [hydef, sq]; group
      _ = t := by rw [he, ← hct]; group
  have hyt : Commute y t := by
    rw [← hy2]
    exact (Commute.refl y).mul_right (Commute.refl y)
  have hyD : y ∈ d.D.map L.subtype ⊔ zpowers t := by
    rw [← hC₁C]
    exact Subgroup.mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 hyt.eq⟩
  apply h.t_not_mem_L
  rw [← hy2]
  rcases (h.mem_sup_zpowers_iff (map_subtype_le d.D)).1 hyD with h1 | h1
  · exact mul_mem (map_subtype_le _ h1) (map_subtype_le _ h1)
  · have e : (t * y) * (t * y) = y * y := by
      calc (t * y) * (t * y) = t * (y * t) * y := by group
        _ = t * (t * y) * y := by rw [hyt.eq]
        _ = (t * t) * (y * y) := by group
        _ = y * y := by rw [h.t_mul_t, one_mul]
    rw [← e]
    exact mul_mem (map_subtype_le _ h1) (map_subtype_le _ h1)

theorem V_le_mhoOne_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    d.V.map L.subtype ≤ mhoOne (yamadaC₁ d t) := by
  have hDC₁ : d.D.map L.subtype ≤ yamadaC₁ d t := le_sup_left.trans (h.tD_le_yamadaC₁ d)
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  have h1 : ((d.x₂ 1 * d.x₅ c : L) : G) ∈ yamadaC₁ d t :=
    hDC₁ ⟨d.x₂ 1 * d.x₅ c, mul_mem (d.x₂_mem_D 1) (d.F_le_D (d.x₅_mem_F c)), rfl⟩
  have h2 : (d.x₂ 1 * d.x₅ c) ^ 2 = d.x₆ c := by
    rw [sq, show d.x₂ 1 * d.x₅ c * (d.x₂ 1 * d.x₅ c) = ⁅d.x₂ 1, d.x₅ c⁆ by
      rw [commutatorElement_def, d.x₂_inv, d.x₅_inv]; group, d.comm₂₅, one_mul]
  have h3 := sq_mem_mhoOne h1
  rw [← SubmonoidClass.coe_pow, h2] at h3
  exact h3

theorem sq_mem_tD_of_mem_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {g : G}
    (hg : g ∈ yamadaC₁ d t) : g ^ 2 ∈ d.D.map L.subtype ⊔ zpowers t := by
  have hK : g ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨yamadaC₁_le d t hg, (h.two_core_C₁_all d).1 hg⟩
  rw [← (h.two_core_C₁_all d).2.1, sq]
  exact Subgroup.mem_inf.2 ⟨mul_mem hg hg, h.crossed_eq_one_iff_D4.1
    (crossed_commutator_sq_eq_one (h.cosetData_tV d) hK hK).2⟩

theorem mhoOne_sup_le_yamadaL₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    mhoOne (yamadaC₁ d t) ⊔ zpowers t ≤ yamadaL₂ d t := by
  refine sup_le (mhoOne_le fun g hg => ?_) ((zpowers_le).2 (h.tM_le_yamadaL₂ d
    (mem_sup_right (mem_zpowers t))))
  rw [sq]
  exact (h.commutator_sq_mem_yamadaL₂ d (h.yamadaC₁_le_yamadaR₂ d hg)
    (h.yamadaC₁_le_yamadaR₂ d hg)).2

theorem leviShort_le_normalizer_mhoOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    d.leviShort ≤ normalizer (((mhoOne (yamadaC₁ d t) ⊔ zpowers t : Subgroup G).comap
      L.subtype ⊓ d.D : Subgroup L) : Set L) := by
  intro l hl
  have hlC := h.L_le_centralizer l.2
  have hlH : (l : G) ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
    h.centralizer_inf_normalizer_V_le d ⟨hlC, map_le_normalizer_map
      d.leviShort_le_normalizer_V ⟨l, hl, rfl⟩⟩
  refine Common.mem_normalizer_inf (mem_normalizer_comap_subtype ?_)
    (d.leviShort_le_normalizer_D hl)
  exact mem_normalizer_sup (le_normalizer_mhoOne _ (le_normalizer_yamadaC₁ d t hlH))
    (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 hlC))

theorem comap_mhoOne_inf_D (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    (mhoOne (yamadaC₁ d t) ⊔ zpowers t : Subgroup G).comap L.subtype ⊓ d.D = d.V := by
  have hVD : d.V ≤ d.D := d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D))
  have hVT : d.V ≤ (mhoOne (yamadaC₁ d t) ⊔ zpowers t : Subgroup G).comap L.subtype ⊓ d.D := by
    refine le_inf (fun v hv => Subgroup.mem_comap.2 (mem_sup_left ?_)) hVD
    exact h.V_le_mhoOne_yamadaC₁ d ⟨v, hv, rfl⟩
  rcases d.leviShort_irreducible_D_mod_V hVT inf_le_right
      (h.leviShort_le_normalizer_mhoOne d) with hT | hT
  · exact hT
  · exfalso
    have h1 : d.x₂ 1 ∈ (mhoOne (yamadaC₁ d t) ⊔ zpowers t : Subgroup G).comap L.subtype ⊓ d.D := by
      rw [hT]
      exact d.x₂_mem_D 1
    exact h.x₂_one_not_mem_yamadaL₂ d (h.mhoOne_sup_le_yamadaL₂ d
      (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 h1).1))

theorem yamada_5_3_5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    mhoOne (yamadaC₁ d t) = d.V.map L.subtype := by
  have hTV := h.comap_mhoOne_inf_D d
  refine le_antisymm (mhoOne_le fun g hg => ?_) (h.V_le_mhoOne_yamadaC₁ d)
  rcases (h.mem_sup_zpowers_iff (map_subtype_le d.D)).1 (h.sq_mem_tD_of_mem_yamadaC₁ d hg) with
    h1 | h1
  · obtain ⟨x, hx, hxe⟩ := h1
    have hxT : x ∈ (mhoOne (yamadaC₁ d t) ⊔ zpowers t : Subgroup G).comap L.subtype ⊓ d.D := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 ?_, hx⟩
      rw [hxe]
      exact mem_sup_left (sq_mem_mhoOne hg)
    rw [hTV] at hxT
    rw [← hxe]
    exact ⟨x, hxT, rfl⟩
  · obtain ⟨x, hx, hxe⟩ := h1
    have hxT : x ∈ (mhoOne (yamadaC₁ d t) ⊔ zpowers t : Subgroup G).comap L.subtype ⊓ d.D := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 ?_, hx⟩
      rw [hxe]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (sq_mem_mhoOne hg))
    rw [hTV] at hxT
    refine absurd ?_ (h.sq_ne_t_mul_of_mem_yamadaC₁ d hg
      (⟨x, hxT, rfl⟩ : L.subtype x ∈ d.V.map L.subtype))
    rw [hxe, ← mul_assoc, h.t_mul_t, one_mul]

end Mho

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
