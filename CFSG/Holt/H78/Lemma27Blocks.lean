module

public import CFSG.Holt.H78.Data
import CFSG.Holt.H78.Lemma27Real

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General Equiv
open scoped Pointwise

section PairProducts

variable {Δ : Type*}

@[expose] def swapSet (N : Subgroup (Perm Δ)) (a b : Δ) : Set (Perm Δ) :=
  {x | x ∈ N ∧ x ∈ longInv (Perm Δ) Δ ∧ x a = b}

@[expose] def pairProducts (N : Subgroup (Perm Δ)) (a b : Δ) : Subgroup (Perm Δ) :=
  Subgroup.closure {g | ∃ x ∈ swapSet N a b, ∃ y ∈ swapSet N a b, x * y = g}

@[simp] theorem mem_swapSet {N : Subgroup (Perm Δ)} {a b : Δ} {x : Perm Δ} :
    x ∈ swapSet N a b ↔ x ∈ N ∧ x ∈ longInv (Perm Δ) Δ ∧ x a = b :=
  Iff.rfl

theorem mul_mem_pairProducts {N : Subgroup (Perm Δ)} {a b : Δ} {x y : Perm Δ}
    (hx : x ∈ swapSet N a b) (hy : y ∈ swapSet N a b) : x * y ∈ pairProducts N a b :=
  Subgroup.subset_closure ⟨x, hx, y, hy, rfl⟩

theorem apply_eq_of_mem_swapSet {N : Subgroup (Perm Δ)} {a b : Δ} {x : Perm Δ}
    (hx : x ∈ swapSet N a b) : x b = a := by
  rw [← hx.2.2, ← Perm.mul_apply, mul_self_eq_one_of_mem_longInv hx.2.1, Perm.one_apply]

theorem pairProducts_le (N : Subgroup (Perm Δ)) (a b : Δ) :
    pairProducts N a b ≤ N ⊓ stabilizer (Perm Δ) a ⊓ stabilizer (Perm Δ) b := by
  rw [pairProducts, Subgroup.closure_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_inf, mem_stabilizer_iff, mem_stabilizer_iff,
    Perm.smul_def, Perm.smul_def, Perm.mul_apply, Perm.mul_apply, hy.2.2,
    apply_eq_of_mem_swapSet hx, apply_eq_of_mem_swapSet hy, hx.2.2]
  exact ⟨⟨N.mul_mem hx.1 hy.1, rfl⟩, rfl⟩

theorem mem_holtDelta_subgroup_perm_iff {N : Subgroup (Perm Δ)} {a b c : Δ} :
    c ∈ holtDelta N Δ a b ↔ ∃ x ∈ swapSet N a b, x c = c := by
  constructor
  · rintro ⟨x, ⟨hxJ, hxa⟩, hxc⟩
    exact ⟨x, ⟨x.2, mem_longInv_subgroup_perm_iff.mp hxJ, hxa⟩, hxc⟩
  · rintro ⟨x, ⟨hxN, hxJ, hxa⟩, hxc⟩
    exact ⟨⟨x, hxN⟩, ⟨mem_longInv_subgroup_perm_iff.mpr hxJ, hxa⟩, hxc⟩

theorem eq_of_mem_holtDelta_self {N : Subgroup (Perm Δ)} {a c : Δ}
    (hc : c ∈ holtDelta N Δ a a) : c = a := by
  obtain ⟨x, ⟨-, hxJ, hxa⟩, hxc⟩ := mem_holtDelta_subgroup_perm_iff.mp hc
  exact hxJ.2.unique hxc hxa

theorem conj_mem_pairProducts_of_forall {N : Subgroup (Perm Δ)} {a b : Δ} {g : Perm Δ}
    (hg : ∀ x ∈ swapSet N a b, g * x * g⁻¹ ∈ swapSet N a b) {p : Perm Δ}
    (hp : p ∈ pairProducts N a b) : g * p * g⁻¹ ∈ pairProducts N a b := by
  have hmap : (pairProducts N a b).map (MulAut.conj g).toMonoidHom ≤ pairProducts N a b := by
    rw [pairProducts, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨_, hg x hx, _, hg y hy, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
  exact hmap ⟨p, hp, rfl⟩

theorem conj_mem_swapSet {N : Subgroup (Perm Δ)} {a b : Δ} {s x : Perm Δ}
    (hs : s ∈ swapSet N a b) (hx : x ∈ swapSet N a b) : s * x * s⁻¹ ∈ swapSet N a b := by
  refine ⟨N.mul_mem (N.mul_mem hs.1 hx.1) (N.inv_mem hs.1), conj_mem_longInv hx.2.1 s, ?_⟩
  rw [Perm.mul_apply, Perm.mul_apply,
    inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_longInv hs.2.1), hs.2.2,
    apply_eq_of_mem_swapSet hx, hs.2.2]

theorem conj_mem_pairProducts_of_mem_swapSet {N : Subgroup (Perm Δ)} {a b : Δ} {s p : Perm Δ}
    (hs : s ∈ swapSet N a b) (hp : p ∈ pairProducts N a b) : s * p * s⁻¹ ∈ pairProducts N a b :=
  conj_mem_pairProducts_of_forall (fun _ hx => conj_mem_swapSet hs hx) hp

end PairProducts

section Alternating

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ]

theorem exists_mem_longInvAt_perm_apply_eq_apply_eq (hodd : Odd (Fintype.card Δ))
    {a b c d e : Δ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ∃ x ∈ longInvAt (Perm Δ) Δ c, x a = b ∧ x d = e := by
  have h3 : 3 ≤ Fintype.card Δ := by
    have h := Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
    exact h ▸ Finset.card_le_univ _
  obtain ⟨s₀, hs₀⟩ := exists_mem_longInvAt_perm hodd h3 c
  obtain ⟨s, hs, hsa⟩ := exists_mem_longInvAt_perm_apply_eq hs₀ hac hbc (Ne.symm hab)
  have hs2 : s * s = 1 := mul_self_eq_one_of_mem_longInv hs.1
  have hsb : s b = a := by rw [← hsa, ← Perm.mul_apply, hs2, Perm.one_apply]
  have hsc : s c = c := hs.2
  have hsd_d : s d ≠ d := fun h => hcd ((apply_eq_self_iff_of_mem_longInvAt_perm hs).mp h).symm
  have hsd_c : s d ≠ c := fun h => hcd (s.injective (hsc.trans h.symm))
  have hsd_b : s d ≠ b := fun h => had (s.injective (hsa.trans h.symm))
  have hsd_a : s d ≠ a := fun h => hbd (s.injective (hsb.trans h.symm))
  refine ⟨swap (s d) e * s * (swap (s d) e)⁻¹, ?_, ?_, ?_⟩
  · have := conj_mem_longInvAt_perm hs (swap (s d) e)
    rwa [swap_apply_of_ne_of_ne hsd_c.symm hce] at this
  · rw [swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hsd_a.symm hae, hsa,
      swap_apply_of_ne_of_ne hsd_b.symm hbe]
  · rw [swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hsd_d.symm hde,
      swap_apply_left]

theorem swap_mul_swap_mem_pairProducts {N : Subgroup (Perm Δ)} (hN : longInv (Perm Δ) Δ ⊆ N)
    (hodd : Odd (Fintype.card Δ)) {a b c d e : Δ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) : swap c e * swap c d ∈ pairProducts N a b := by
  obtain ⟨x, hx, hxa, hxd⟩ :=
    exists_mem_longInvAt_perm_apply_eq_apply_eq hodd hab hac had hae hbc hbd hbe hcd hce hde
  have hx2 : x * x = 1 := mul_self_eq_one_of_mem_longInv hx.1
  have hy : swap c d * x * (swap c d)⁻¹ ∈ longInv (Perm Δ) Δ := conj_mem_longInv hx.1 _
  have hya : (swap c d * x * (swap c d)⁻¹) a = b := by
    rw [swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hac had, hxa,
      swap_apply_of_ne_of_ne hbc hbd]
  have hxy : x * (swap c d * x * (swap c d)⁻¹) = swap c e * swap c d := by
    have h1 : x * swap c d * x⁻¹ = swap c e := by
      rw [← swap_apply_apply, show x c = c from hx.2, hxd]
    rw [inv_eq_of_mul_eq_one_right hx2] at h1
    rw [swap_inv, ← h1]
    group
  rw [← hxy]
  exact mul_mem_pairProducts ⟨hN hx.1, hx.1, hxa⟩ ⟨hN hy, hy, hya⟩

omit [Fintype Δ] [DecidableEq Δ] in
theorem conj_mem_pairProducts {N : Subgroup (Perm Δ)} (hN : longInv (Perm Δ) Δ ⊆ N) {a b : Δ}
    {g : Perm Δ} (hga : g a = a) (hgb : g b = b) {p : Perm Δ} (hp : p ∈ pairProducts N a b) :
    g * p * g⁻¹ ∈ pairProducts N a b := by
  refine conj_mem_pairProducts_of_forall (fun z hz => ⟨hN (conj_mem_longInv hz.2.1 g),
    conj_mem_longInv hz.2.1 g, ?_⟩) hp
  rw [Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq.mpr hga.symm, hz.2.2, hgb]

theorem alternatingGroup_inf_stabilizer_le_pairProducts {N : Subgroup (Perm Δ)}
    (hN : longInv (Perm Δ) Δ ⊆ N) (hodd : Odd (Fintype.card Δ)) {a b : Δ} (hab : a ≠ b) :
    alternatingGroup Δ ⊓ stabilizer (Perm Δ) a ⊓ stabilizer (Perm Δ) b ≤ pairProducts N a b := by
  intro m hm
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_stabilizer_iff, mem_stabilizer_iff] at hm
  obtain ⟨⟨hmA, hma⟩, hmb⟩ := hm
  have hma' : m a = a := hma
  have hmb' : m b = b := hmb
  have h₁ : ∀ x, (m x ≠ a ∧ m x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := fun x => by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (h ▸ hma'), fun h => h2 (h ▸ hmb')⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (m.injective (h.trans hma'.symm)),
        fun h => h2 (m.injective (h.trans hmb'.symm))⟩
  have h₂ : ∀ x, m x ≠ x → x ≠ a ∧ x ≠ b := fun x hx =>
    ⟨fun h => hx (h ▸ hma'), fun h => hx (h ▸ hmb')⟩
  have hsub : m.subtypePerm h₁ ∈
      Subgroup.closure {σ : Perm {x // x ≠ a ∧ x ≠ b} | σ.IsThreeCycle} := by
    rw [Perm.closure_three_cycles_eq_alternating, Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype,
      Perm.ofSubtype_subtypePerm h₁ h₂]
    exact hmA
  have hle : Subgroup.closure {σ : Perm {x // x ≠ a ∧ x ≠ b} | σ.IsThreeCycle} ≤
      (pairProducts N a b).comap (Perm.ofSubtype : Perm {x // x ≠ a ∧ x ≠ b} →* Perm Δ) := by
    rw [Subgroup.closure_le]
    intro σ hσ
    have hσ' : σ.IsThreeCycle := hσ
    obtain ⟨c, d, e, hcd, hce, hde, -⟩ := Finset.card_eq_three.mp hσ'.card_support
    have h0 : (swap c e * swap c d).IsThreeCycle :=
      Perm.isThreeCycle_swap_mul_swap_same hce hcd hde.symm
    obtain ⟨g, rfl⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr
      ((show (swap c e * swap c d).cycleType = {3} from h0).trans
        (show σ.cycleType = {3} from hσ').symm))
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    simp only [map_mul, map_inv, Perm.ofSubtype_swap_eq]
    refine conj_mem_pairProducts hN (Perm.ofSubtype_apply_of_not_mem g fun h => h.1 rfl)
      (Perm.ofSubtype_apply_of_not_mem g fun h => h.2 rfl) ?_
    exact swap_mul_swap_mem_pairProducts hN hodd hab c.2.1.symm d.2.1.symm e.2.1.symm
      c.2.2.symm d.2.2.symm e.2.2.symm (fun h => hcd (Subtype.ext h))
      (fun h => hce (Subtype.ext h)) (fun h => hde (Subtype.ext h))
  have := hle hsub
  rwa [Subgroup.mem_comap, Perm.ofSubtype_subtypePerm h₁ h₂] at this

theorem pairProducts_eq_of_alternatingGroup_le {N : Subgroup (Perm Δ)}
    (hAN : alternatingGroup Δ ≤ N) {s : Perm Δ} (hsN : s ∈ N) (hs : s ∈ longInv (Perm Δ) Δ)
    {a b : Δ} (hab : a ≠ b) :
    pairProducts N a b = alternatingGroup Δ ⊓ stabilizer (Perm Δ) a ⊓ stabilizer (Perm Δ) b := by
  refine le_antisymm (fun g hg => ?_) (alternatingGroup_inf_stabilizer_le_pairProducts
    (longInv_perm_subset_of_alternatingGroup_le hAN hsN hs) (odd_card_of_mem_longInv_perm hs) hab)
  have hle : pairProducts N a b ≤ alternatingGroup Δ := by
    rw [pairProducts, Subgroup.closure_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, Perm.mem_alternatingGroup, Perm.sign_mul,
      sign_eq_of_mem_longInv_perm hx.2.1 hy.2.1, Int.units_mul_self]
  have h := pairProducts_le N a b hg
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at h ⊢
  exact ⟨⟨hle hg, h.1.2⟩, h.2⟩

end Alternating

namespace HoltData

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem rho_mem_swapSet {α β : Ω} {u : jHull G Ω} (hu : (u : G) ∈ longInvSwap G Ω α β)
    (i : D.ι) : D.ρ i u ∈ swapSet (D.ρ i).range (D.coord α i) (D.coord β i) :=
  ⟨⟨u, rfl⟩, D.rho_mem_longInv hu.1 i, by rw [← D.coord_smul, hu.2]⟩

theorem coord_mem_holtDelta {α β γ : Ω} (hγ : γ ∈ holtDelta G Ω α β) (i : D.ι) :
    D.coord γ i ∈ holtDelta (D.ρ i).range (D.Ψc i) (D.coord α i) (D.coord β i) := by
  obtain ⟨u, hu, huγ⟩ := hγ
  rw [mem_holtDelta_subgroup_perm_iff]
  refine ⟨_, D.rho_mem_swapSet (u := ⟨u, mem_jHull_of_mem_longInv hu.1⟩) hu i, ?_⟩
  rw [← D.coord_smul]
  exact congrArg (D.coord · i) huγ

theorem holtDelta_range_rho_self {i : D.ι} (a : D.Ψc i) :
    holtDelta (D.ρ i).range (D.Ψc i) a a = {a} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, fun c hc => eq_of_mem_holtDelta_self hc⟩
  have hτ := D.rho_mem_longInv D.t_mem i
  obtain ⟨C, hC, -⟩ := hτ.2
  obtain ⟨g, hg⟩ := (D.factor i).isPretransitive.exists_smul_eq C a
  have hgN : (g : Perm (D.Ψc i)) ∈ (D.ρ i).range := Subgroup.map_le_range _ _ g.2
  have hτa : ((g : Perm (D.Ψc i)) * D.ρ i D.tHull * (g : Perm (D.Ψc i))⁻¹) a = a := by
    rw [Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq.mpr hg.symm,
      show D.ρ i D.tHull C = C from hC]
    exact hg
  rw [mem_holtDelta_subgroup_perm_iff]
  exact ⟨_, ⟨mul_mem (mul_mem hgN ⟨D.tHull, rfl⟩) (inv_mem hgN), conj_mem_longInv hτ _, hτa⟩, hτa⟩

theorem holtDelta_range_rho_eq_compl {i : D.ι} (hi : D.M i = alternatingGroup (D.Ψc i))
    {a b : D.Ψc i} (hab : a ≠ b) : holtDelta (D.ρ i).range (D.Ψc i) a b = {a, b}ᶜ := by
  have h : D.M i ≤ (D.ρ i).range := Subgroup.map_le_range _ _
  rw [hi] at h
  exact holtDelta_eq_compl_of_alternatingGroup_le h ⟨D.tHull, rfl⟩ (D.rho_mem_longInv D.t_mem i)
    hab

theorem coord_holtDelta_eq (α β : Ω) :
    D.coord '' holtDelta G Ω α β =
      Set.univ.pi fun i => holtDelta (D.ρ i).range (D.Ψc i) (D.coord α i) (D.coord β i) := by
  ext c
  constructor
  · rintro ⟨γ, hγ, rfl⟩ i -
    exact D.coord_mem_holtDelta hγ i
  · intro hc
    simp only [Set.mem_pi, Set.mem_univ, true_implies, mem_holtDelta_subgroup_perm_iff] at hc
    choose x hx hxc using hc
    obtain ⟨u, hu, hρ⟩ := D.exists_mem_longInvSwap_rho_eq x (fun i => (hx i).1)
      (fun i => (hx i).2.1) fun i => (hx i).2.2
    obtain ⟨γ₀, hγ₀⟩ := exists_mem_longInvAt hu.1
    obtain ⟨ω, rfl⟩ := D.coord_surjective c
    refine ⟨γ₀, ⟨u, hu, hγ₀.2⟩, ?_⟩
    have hfix : D.coord ((u : G) • ω) = D.coord ω := funext fun i => by
      rw [D.coord_smul, hρ, hxc]
    exact ((D.coord_smul_eq_iff hγ₀ ω).mp hfix).symm

end HoltData

theorem relIndex_sup_zpowers_le_two {X : Type*} [Group X] {A : Subgroup X} {s : X}
    (hs : s * s = 1) (hsA : ∀ p ∈ A, s * p * s⁻¹ ∈ A) :
    A.relIndex (A ⊔ Subgroup.zpowers s) ≤ 2 := by
  have hsN : s ∈ Subgroup.normalizer (A : Set X) := Subgroup.mem_normalizer_iff.mpr fun p =>
    ⟨hsA p, fun h => by
      have h1 := hsA _ h
      rwa [show s * (s * p * s⁻¹) * s⁻¹ = p by
        rw [inv_eq_of_mul_eq_one_right hs]
        calc s * (s * p * s) * s = (s * s) * p * (s * s) := by group
          _ = p := by rw [hs, one_mul, mul_one]] at h1⟩
  have hle : A ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (A : Set X) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hsN)
  have := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hle
  set s' : ↥(A ⊔ Subgroup.zpowers s) := ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩
  have hsup : A.subgroupOf (A ⊔ Subgroup.zpowers s) ⊔ Subgroup.zpowers s' = ⊤ := by
    apply Subgroup.map_injective (A ⊔ Subgroup.zpowers s).subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left le_sup_left, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  rw [Subgroup.relIndex, ← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_left,
    ← Subgroup.inf_relIndex_right]
  have h2 : orderOf s' ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
    rw [Subgroup.coe_pow, sq]
    exact hs))
  refine Nat.le_of_dvd two_pos ((Subgroup.relIndex_dvd_card _ _).trans ?_)
  rwa [Nat.card_zpowers]

namespace HoltData

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem pi_pairProducts_le_map_closure {α β : Ω} (hne : (longInvSwap G Ω α β).Nonempty) :
    Subgroup.pi Set.univ (fun i => pairProducts (D.ρ i).range (D.coord α i) (D.coord β i)) ≤
      (Subgroup.closure ((↑) ⁻¹' longInvSwap G Ω α β : Set (jHull G Ω))).map
        (MonoidHom.pi D.ρ) := by
  obtain ⟨s, hs⟩ := hne
  have hc := fun i => D.rho_mem_swapSet (u := ⟨s, mem_jHull_of_mem_longInv hs.1⟩) hs i
  have hupd : ∀ (i : D.ι) (z : Perm (D.Ψc i)),
      z ∈ swapSet (D.ρ i).range (D.coord α i) (D.coord β i) → ∀ j,
        Function.update (fun j => D.ρ j ⟨s, mem_jHull_of_mem_longInv hs.1⟩) i z j ∈
          swapSet (D.ρ j).range (D.coord α j) (D.coord β j) := by
    intro i z hz j
    rcases eq_or_ne j i with rfl | hji
    · rw [Function.update_self]
      exact hz
    · rw [Function.update_of_ne hji]
      exact hc j
  rw [Subgroup.pi_le_iff]
  intro i
  rw [pairProducts, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  obtain ⟨u, hu, hρu⟩ := D.exists_mem_longInvSwap_rho_eq _ (fun j => (hupd i x hx j).1)
    (fun j => (hupd i x hx j).2.1) fun j => (hupd i x hx j).2.2
  obtain ⟨v, hv, hρv⟩ := D.exists_mem_longInvSwap_rho_eq _ (fun j => (hupd i y hy j).1)
    (fun j => (hupd i y hy j).2.1) fun j => (hupd i y hy j).2.2
  refine ⟨u * v⁻¹, mul_mem (Subgroup.subset_closure hu) (inv_mem (Subgroup.subset_closure hv)),
    funext fun j => ?_⟩
  rw [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, MonoidHom.pi_apply, MonoidHom.pi_apply, hρu j,
    hρv j, MonoidHom.mulSingle_apply]
  rcases eq_or_ne j i with rfl | hji
  · rw [Function.update_self, Function.update_self, Pi.mulSingle_eq_same,
      inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_longInv hy.2.1)]
  · rw [Function.update_of_ne hji, Function.update_of_ne hji, mul_inv_cancel,
      Pi.mulSingle_eq_of_ne hji]

theorem map_closure_longInvSwap_eq {α β : Ω} {s : jHull G Ω}
    (hs : (s : G) ∈ longInvSwap G Ω α β) :
    (Subgroup.closure ((↑) ⁻¹' longInvSwap G Ω α β : Set (jHull G Ω))).map (MonoidHom.pi D.ρ) =
      Subgroup.pi Set.univ (fun i => pairProducts (D.ρ i).range (D.coord α i) (D.coord β i)) ⊔
        Subgroup.zpowers (MonoidHom.pi D.ρ s) := by
  refine le_antisymm ?_ (sup_le (D.pi_pairProducts_le_map_closure ⟨s, hs⟩)
    (Subgroup.zpowers_le.mpr ⟨s, Subgroup.subset_closure hs, rfl⟩))
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨u, hu, rfl⟩
  rw [SetLike.mem_coe, ← inv_mul_cancel_right (MonoidHom.pi D.ρ u) (MonoidHom.pi D.ρ s)]
  refine mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_pi _).mpr fun i _ => ?_))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  rw [Pi.mul_apply, Pi.inv_apply, MonoidHom.pi_apply, MonoidHom.pi_apply,
    inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_longInv (D.rho_mem_swapSet hs i).2.1)]
  exact mul_mem_pairProducts (D.rho_mem_swapSet hu i) (D.rho_mem_swapSet hs i)

theorem relIndex_pi_pairProducts_le_two {α β : Ω} {s : jHull G Ω}
    (hs : (s : G) ∈ longInvSwap G Ω α β) :
    (Subgroup.pi Set.univ fun i => pairProducts (D.ρ i).range (D.coord α i) (D.coord β i)).relIndex
      ((Subgroup.closure ((↑) ⁻¹' longInvSwap G Ω α β : Set (jHull G Ω))).map
        (MonoidHom.pi D.ρ)) ≤ 2 := by
  rw [D.map_closure_longInvSwap_eq hs]
  refine relIndex_sup_zpowers_le_two (funext fun i => ?_) fun p hp =>
    (Subgroup.mem_pi _).mpr fun i _ => ?_
  · exact mul_self_eq_one_of_mem_longInv (D.rho_mem_swapSet hs i).2.1
  · exact conj_mem_pairProducts_of_mem_swapSet (D.rho_mem_swapSet hs i)
      ((Subgroup.mem_pi _).mp hp i trivial)

end HoltData

end CFSG.Holt.H78
