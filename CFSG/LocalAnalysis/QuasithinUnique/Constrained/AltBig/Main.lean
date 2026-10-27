module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Swap
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement Pointwise

variable {α : Type} [Fintype α] [DecidableEq α]

theorem step1Aux_third (p : FpfInv α) (hα : 4 ≤ Fintype.card α) (z : α) :
    ∃ y, y ≠ z ∧ y ≠ p.μ z := by
  by_contra hcon
  have hcon' : ∀ y, y ≠ z → y = p.μ z := fun y hy => by
    by_contra hy'
    exact hcon ⟨y, hy, hy'⟩
  have hsub : (Finset.univ : Finset α) ⊆ {z, p.μ z} := by
    intro y _
    by_cases hy : y = z
    · simp [hy]
    · simp [hcon' y hy]
  have h1 := Finset.card_le_card hsub
  have h2 : ({z, p.μ z} : Finset α).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ] at h1
  omega

theorem step1Aux_mu_mem (p : FpfInv α) (hα : 4 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {S : Set α} (hS : ∀ y ∈ Y, ∀ z ∈ S, y z ∈ S) {z : α} (hz : z ∈ S) :
    p.μ z ∈ S := by
  obtain ⟨y, hyz, hyμ⟩ := step1Aux_third p hα z
  have hg : swap z (p.μ z) * swap y (p.μ y) ∈ Y := hB z y hyz hyμ
  have hfix : swap y (p.μ y) z = z := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact fun h => hyz h.symm
    · intro h
      apply hyμ
      rw [h, p.inv]
  have key := hS _ hg z hz
  rw [Equiv.Perm.mul_apply, hfix, Equiv.swap_apply_left] at key
  exact key

theorem step1Aux_normal {Y : Subgroup (Perm α)} {S : Set α}
    (hS : ∀ y ∈ Y, ∀ z ∈ S, y z ∈ S) : ((Y ⊓ fixOn S).subgroupOf Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnY, hnF⟩ := Subgroup.mem_inf.mp hn
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  refine Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.mul_mem g.2 hnY) (Y.inv_mem g.2), ?_⟩
  refine mem_fixOn.mpr fun z hz => ?_
  have hz' : (g : Perm α)⁻¹ z ∈ S := hS _ (Y.inv_mem g.2) z hz
  simp only [Equiv.Perm.mul_apply]
  rw [mem_fixOn.mp hnF _ hz', Equiv.Perm.inv_def, Equiv.apply_symm_apply]

theorem step1Aux_sub {Y : Subgroup (Perm α)} {S : Set α}
    (hS : ∀ y ∈ Y, ∀ z ∈ S, y z ∈ S) : CFSG.Open.IsSubnormal (Y ⊓ fixOn S) Y :=
  CFSG.Open.IsSubnormal.step inf_le_left (step1Aux_normal hS) (CFSG.Open.IsSubnormal.refl Y)

theorem step1 (p : FpfInv α) (hα : 4 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {E : Subgroup (Perm α)} (hE : IsComponentOf E Y) {S : Set α}
    (hS : ∀ y ∈ Y, ∀ z ∈ S, y z ∈ S) (hmove : ∃ e ∈ E, ∃ z ∈ S, e z ≠ z) :
    ∀ e ∈ E, ∀ z, z ∉ S → e z = z := by
  have hperf : ⁅E, E⁆ = E := quasisimple_comm_eq hE.2.2
  have hWcl : ∀ x ∈ (Sᶜ : Set α), p.μ x ∈ (Sᶜ : Set α) := by
    intro x hx
    rw [Set.mem_compl_iff] at hx ⊢
    intro hmx
    apply hx
    have := step1Aux_mu_mem p hα hB hS hmx
    rwa [p.inv] at this
  have hEW : ∀ e ∈ E, ∀ x ∈ (Sᶜ : Set α), e x ∈ (Sᶜ : Set α) := by
    intro e he x hx
    rw [Set.mem_compl_iff] at hx ⊢
    intro hex
    apply hx
    have hinv : e⁻¹ ∈ Y := hE.1 (E.inv_mem he)
    have := hS _ hinv _ hex
    rwa [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at this
  have hsep : ∀ w, w ∉ S → ∀ z ∈ S, z ≠ w ∧ z ≠ p.μ w := by
    intro w hw z hz
    refine ⟨fun h => hw (by rw [← h]; exact hz), fun h => hw ?_⟩
    have := step1Aux_mu_mem p hα hB hS hz
    rw [h, p.inv] at this
    exact this
  have hσ : ∀ x ∈ (Sᶜ : Set α), ∀ y ∈ (Sᶜ : Set α), y ≠ x → y ≠ p.μ x →
      swap x (p.μ x) * swap y (p.μ y) ∈ Y ⊓ fixOn S := by
    intro x hx y hy hyx hyμ
    rw [Set.mem_compl_iff] at hx hy
    refine Subgroup.mem_inf.mpr ⟨hB x y hyx hyμ, mem_fixOn.mpr fun z hz => ?_⟩
    obtain ⟨hzy, hzμy⟩ := hsep y hy z hz
    obtain ⟨hzx, hzμx⟩ := hsep x hx z hz
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzy hzμy,
      Equiv.swap_apply_of_ne_of_ne hzx hzμx]
  have hcomm : ⁅E, Y ⊓ fixOn S⁆ = ⊥ := by
    rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hE (step1Aux_sub hS) with h | h
    · exfalso
      obtain ⟨e, he, z, hz, hez⟩ := hmove
      exact hez (mem_fixOn.mp (Subgroup.mem_inf.mp (h he)).2 z hz)
    · exact h
  have hcommute : ∀ e ∈ E, ∀ x ∈ (Sᶜ : Set α), ∀ y ∈ (Sᶜ : Set α), y ≠ x → y ≠ p.μ x →
      Commute e (swap x (p.μ x) * swap y (p.μ y)) := by
    intro e he x hx y hy hyx hyμ
    have h1 : ⁅e, swap x (p.μ x) * swap y (p.μ y)⁆ ∈ ⁅E, Y ⊓ fixOn S⁆ :=
      Subgroup.commutator_mem_commutator he (hσ x hx y hy hyx hyμ)
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  by_cases hsmall : Nat.card (Sᶜ : Set α) ≤ 4
  · intro e he z hz
    exact perfect_fix_small hperf hsmall hEW e he z hz
  · obtain ⟨r, hr⟩ := even_card_of_closed p Sᶜ hWcl
    have h6 : 6 ≤ Nat.card (Sᶜ : Set α) := by omega
    have hpairs : ∀ e ∈ E, ∀ x ∈ (Sᶜ : Set α), e x = x ∨ e x = p.μ x := fun e he =>
      fix_pairs_of_commute p hWcl h6 (hcommute e he)
    intro e he z hz
    exact perfect_fix_pairs p hperf hpairs hWcl e he z hz

theorem generic_component (p : FpfInv α) (hα : 4 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {E : Subgroup (Perm α)} (hE : IsComponentOf E Y) {x : α}
    (hx : ∃ e ∈ E, e x ≠ x) (hS : MulAction.orbit (↥Y) x ≠ Set.univ) :
    ∃ k, Even k ∧ 5 ≤ k ∧ k ≤ Fintype.card α ∧ Nonempty (↥E ≃* alternatingGroup (Fin k)) := by
  classical
  set S : Set α := MulAction.orbit (↥Y) x with hSdef
  have hSinv : ∀ y ∈ Y, ∀ z ∈ S, y z ∈ S := by
    intro y hy z hz
    obtain ⟨g, rfl⟩ := hz
    exact ⟨⟨y, hy⟩ * g, by simp [mul_smul]⟩
  have hmoveS : ∃ e ∈ E, ∃ z ∈ S, e z ≠ z := by
    obtain ⟨e, he, hne⟩ := hx
    exact ⟨e, he, x, MulAction.mem_orbit_self x, hne⟩
  have htriv := step1 p hα hB hE hSinv hmoveS
  have horb_eq : ∀ z ∈ S, MulAction.orbit (↥Y) z = S := fun z hz => MulAction.orbit_eq_iff.2 hz
  have hμS : ∀ z ∈ S, p.μ z ∈ S := by
    intro z hz
    have h1 := orbit_mu_mem p hα hB z
    rwa [horb_eq z hz] at h1
  have hiff : ∀ z, p.μ z ∈ S ↔ z ∈ S := fun z =>
    ⟨fun h => by simpa [p.inv] using hμS _ h, hμS z⟩
  let q : FpfInv ↥S :=
    ⟨p.μ.subtypePerm hiff, by intro z; ext; simp [p.inv],
      by intro z h; apply p.fpf z.1; exact congrArg Subtype.val h⟩
  let ρ : ↥Y →* Perm ↥S := MulAction.toPermHom ↥Y ↥S
  have hρ : ∀ (g : ↥Y) (t : ↥S), ((ρ g t : ↥S) : α) = (g : Perm α) t := fun g t => rfl
  have hq : ∀ z : ↥S, swap z (q.μ z) ∈ ρ.range := by
    intro z
    obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
      by_contra h
      push Not at h
      exact hS (Set.eq_univ_of_forall h)
    have hwz : w ≠ z.1 := fun h => hw (h ▸ z.2)
    have hwμ : w ≠ p.μ z.1 := fun h => hw (h ▸ hμS z.1 z.2)
    have hμw : p.μ w ∉ S := fun h => hw (by simpa [p.inv] using hμS _ h)
    have hσ : swap z.1 (p.μ z.1) * swap w (p.μ w) ∈ Y := hB z.1 w hwz hwμ
    refine ⟨⟨_, hσ⟩, ?_⟩
    apply Equiv.ext
    intro t
    apply Subtype.ext
    have h1 : swap w (p.μ w) t.1 = t.1 := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; exact hw (h ▸ t.2)
      · intro h; exact hμw (h ▸ t.2)
    show (swap z.1 (p.μ z.1) * swap w (p.μ w) : Perm α) t.1 = _
    rw [Perm.mul_apply, h1]
    rw [coe_swap_subtype]
    rfl
  let φ : ↥(E.subgroupOf Y) →* Perm ↥S := ρ.comp (E.subgroupOf Y).subtype
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgE : ((g : ↥Y) : Perm α) ∈ E := g.2
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro z
    show ((g : ↥Y) : Perm α) z = z
    by_cases hz : z ∈ S
    · have h2 := congrArg (fun f : Perm ↥S => ((f ⟨z, hz⟩ : ↥S) : α)) hg
      simpa [φ, hρ] using h2
    · exact htriv _ hgE z hz
  have hsubY : IsSubnormal (E.subgroupOf Y) ⊤ := by
    have h := CFSG.Quasithin.A3.subnormal_comap Y.subtype hE.2.1
    rwa [show Y.comap Y.subtype = ⊤ from Subgroup.subgroupOf_self Y] at h
  have hE'sub : IsSubnormal φ.range ρ.range := by
    have h := CFSG.Quasithin.A3.subnormal_map ρ hsubY
    rw [← MonoidHom.range_eq_map] at h
    have hr : φ.range = (E.subgroupOf Y).map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hr]
    exact h
  have isoE : ↥E ≃* ↥φ.range :=
    (Subgroup.subgroupOfEquivOfLe hE.1).symm.trans (MonoidHom.ofInjective hφinj)
  have hE' : IsComponentOf φ.range ρ.range :=
    ⟨by rintro _ ⟨g, rfl⟩; exact ⟨(g : ↥Y), rfl⟩, hE'sub,
      open_isQuasisimple_of_mulEquiv isoE hE.2.2⟩
  obtain ⟨C, hC5, hCμ, hEC⟩ := tc q hq hE'
  refine ⟨C.card, ?_, hC5, ?_, ?_⟩
  · have h1 := even_card_of_closed q (C : Set ↥S) (fun x hx => hCμ x hx)
    simpa [Nat.card_eq_fintype_card] using h1
  · calc C.card ≤ Fintype.card ↥S := Finset.card_le_univ C
      _ ≤ Fintype.card α := Fintype.card_subtype_le _
  · obtain ⟨eAlt⟩ := altOn_equiv C
    exact ⟨isoE.trans ((MulEquiv.subgroupCongr hEC).trans (eAlt.trans
      (Equiv.altCongrHom (Fintype.equivFinOfCardEq (Fintype.card_coe C)))))⟩

def normClos (Y E : Subgroup (Perm α)) : Subgroup (Perm α) :=
  (Subgroup.normalClosure ((E.subgroupOf Y : Subgroup ↥Y) : Set ↥Y)).map Y.subtype

theorem normClos_le (Y E : Subgroup (Perm α)) : normClos Y E ≤ Y := by
  unfold normClos
  exact Subgroup.map_subtype_le _

theorem normClos_normal (Y E : Subgroup (Perm α)) : ((normClos Y E).subgroupOf Y).Normal := by
  have h : (normClos Y E).subgroupOf Y =
      Subgroup.normalClosure ((E.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    unfold normClos
    exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  rw [h]
  infer_instance

theorem le_normClos {Y E : Subgroup (Perm α)} (hEY : E ≤ Y) : E ≤ normClos Y E := by
  intro e he
  have hmem : (⟨e, hEY he⟩ : ↥Y) ∈ ((E.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := he
  have hn := Subgroup.subset_normalClosure hmem
  unfold normClos
  exact Subgroup.mem_map.mpr ⟨⟨e, hEY he⟩, hn, rfl⟩

theorem normClos_le_of_normal {Y E M : Subgroup (Perm α)} (hM : M ≤ Y)
    (hn : (M.subgroupOf Y).Normal) (hEM : E ≤ M) : normClos Y E ≤ M := by
  unfold normClos
  rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_subtype]
  apply Subgroup.normalClosure_le_normal
  intro x hx
  exact hEM (show (x : Perm α) ∈ E from hx)

theorem orbit_isBlock {Y N : Subgroup (Perm α)} (hNY : N ≤ Y) (hn : (N.subgroupOf Y).Normal)
    (x : α) : MulAction.IsBlock (↥Y) (MulAction.orbit (↥N) x) := by
  have hB : MulAction.IsBlock (↥Y) (MulAction.orbit (↥(N.subgroupOf Y)) x) :=
    MulAction.IsBlock.orbit_of_normal x
  have heq : MulAction.orbit (↥(N.subgroupOf Y)) x = MulAction.orbit (↥N) x := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨((g : ↥Y) : Perm α), Subgroup.mem_subgroupOf.mp g.2⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨⟨⟨(h : Perm α), hNY h.2⟩, Subgroup.mem_subgroupOf.mpr h.2⟩, rfl⟩
  rw [heq] at hB
  exact hB

theorem fong_swap_mul_swap_fix_or_mu (p : FpfInv α) {x y : α} (hyx : y ≠ x) (hyμ : y ≠ p.μ x)
    (t : α) :
    (swap x (p.μ x) * swap y (p.μ y)) t = t ∨ (swap x (p.μ x) * swap y (p.μ y)) t = p.μ t := by
  have hxy : x ≠ y := fun h => hyx h.symm
  have hμxy : p.μ x ≠ y := fun h => hyμ h.symm
  have hxμy : x ≠ p.μ y := fun h => hyμ (by rw [h, p.inv])
  have hμyx : p.μ y ≠ x := fun h => hyμ (by rw [← h, p.inv])
  have hμxμy : p.μ x ≠ p.μ y := fun h => hxy (p.μ.injective h)
  have hμyμx : p.μ y ≠ p.μ x := fun h => hyx (p.μ.injective h)
  by_cases h1 : t = x
  · right
    rw [h1, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxy hxμy, Equiv.swap_apply_left]
  by_cases h2 : t = p.μ x
  · right
    rw [h2, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hμxy hμxμy,
      Equiv.swap_apply_right, p.inv]
  by_cases h3 : t = y
  · right
    rw [h3, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hμyx hμyμx]
  by_cases h4 : t = p.μ y
  · right
    rw [h4, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hyx hyμ,
      p.inv]
  left
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h3 h4,
    Equiv.swap_apply_of_ne_of_ne h1 h2]

open scoped Pointwise in
theorem fong_smul_eq_of_mu_closed {G : Type*} [Group G] [MulAction G α] (p : FpfInv α) {σ : G}
    (hσ : ∀ t, σ • t = t ∨ σ • t = p.μ t) {T : Set α} (hT : ∀ t ∈ T, p.μ t ∈ T) :
    σ • T = T := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have hσs : σ • (σ⁻¹ • z) = z := smul_inv_smul σ z
  have hs := hσ (σ⁻¹ • z)
  rw [hσs] at hs
  constructor
  · intro h
    rcases hs with h1 | h1
    · rw [h1]
      exact h
    · rw [h1]
      exact hT _ h
  · intro h
    rcases hs with h1 | h1
    · rw [← h1]
      exact h
    · have e : p.μ z = σ⁻¹ • z := by
        have h2 := congrArg (⇑p.μ) h1
        rw [p.inv] at h2
        exact h2
      rw [← e]
      exact hT z h

open scoped Pointwise in
theorem primitive_of_normal_transitive (p : FpfInv α) (h6 : 6 ≤ Fintype.card α)
    {Y : Subgroup (Perm α)} (hB : p.Contained Y) {E : Subgroup (Perm α)}
    (hE : IsComponentOf E Y) (hNt : MulAction.IsPretransitive ↥(normClos Y E) α) :
    MulAction.IsPreprimitive ↥Y α := by
  have hYt : MulAction.IsPretransitive ↥Y α :=
    ⟨fun a b => by
      obtain ⟨n, hn⟩ := hNt.exists_smul_eq a b
      exact ⟨⟨(n : Perm α), normClos_le Y E n.2⟩, hn⟩⟩
  refine { toIsPretransitive := hYt, isTrivialBlock_of_isBlock := ?_ }
  intro B hBl
  unfold MulAction.IsTrivialBlock
  by_cases hs : B.Subsingleton
  · exact Or.inl hs
  right
  have hnt : ∃ a ∈ B, ∃ b ∈ B, a ≠ b := Set.not_subsingleton_iff.mp hs
  have hclos : ∀ g : ↥Y, ∀ t ∈ g • B, p.μ t ∈ g • B := by
    intro g
    refine block_closed p h6 hB (hBl.translate g) ?_
    obtain ⟨a, ha, b, hb, hab⟩ := hnt
    exact ⟨g • a, Set.smul_mem_smul_set ha, g • b, Set.smul_mem_smul_set hb,
      fun h => hab ((smul_left_cancel_iff g).mp h)⟩
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (Perm α),
      M = (MulAction.stabilizer ↥Y B).normalCore.map Y.subtype := ⟨_, rfl⟩
  have hMY : M ≤ Y := by
    rw [hM]
    rintro _ ⟨s, _, rfl⟩
    exact s.2
  have hMn : (M.subgroupOf Y).Normal := by
    have hEq : M.subgroupOf Y = (MulAction.stabilizer ↥Y B).normalCore := by
      rw [hM]
      exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
    rw [hEq]
    infer_instance
  have hMstab : ∀ m ∈ M, m • B = B := by
    intro m hm
    rw [hM] at hm
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hm
    exact (MulAction.mem_stabilizer_iff (G := ↥Y)).mp (Subgroup.normalCore_le _ hs)
  have hσM : ∀ x y : α, y ≠ x → y ≠ p.μ x → swap x (p.μ x) * swap y (p.μ y) ∈ M := by
    intro x y hyx hyμ
    obtain ⟨s, hs⟩ : ∃ s : ↥Y, (s : Perm α) = swap x (p.μ x) * swap y (p.μ y) :=
      ⟨⟨_, hB x y hyx hyμ⟩, rfl⟩
    have hσfix : ∀ t, s • t = t ∨ s • t = p.μ t := by
      intro t
      change (s : Perm α) t = t ∨ (s : Perm α) t = p.μ t
      rw [hs]
      exact fong_swap_mul_swap_fix_or_mu p hyx hyμ t
    rw [hM]
    refine Subgroup.mem_map.mpr ⟨s, ?_, hs⟩
    refine fun g => ?_
    rw [MulAction.mem_stabilizer_iff]
    have hT : s • (g⁻¹ • B) = g⁻¹ • B := fong_smul_eq_of_mu_closed p hσfix (hclos g⁻¹)
    rw [mul_smul, mul_smul, hT, smul_inv_smul]
  have hsub : CFSG.Open.IsSubnormal M Y :=
    CFSG.Open.IsSubnormal.step hMY hMn (CFSG.Open.IsSubnormal.refl Y)
  rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hE hsub with hEM | hcomm
  ·
    obtain ⟨a, ha, -⟩ := hnt
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨n, hn⟩ := hNt.exists_smul_eq a z
    have hnB : (n : Perm α) • B = B := hMstab _ (normClos_le_of_normal hMY hMn hEM n.2)
    have hz : z ∈ (n : Perm α) • B := Set.mem_smul_set.mpr ⟨a, ha, hn⟩
    rw [hnB] at hz
    exact hz
  ·
    exfalso
    have hcommE : ∀ e ∈ E, ∀ x y : α, y ≠ x → y ≠ p.μ x →
        Commute e (swap x (p.μ x) * swap y (p.μ y)) := by
      intro e he x y hyx hyμ
      have hmem : ⁅e, swap x (p.μ x) * swap y (p.μ y)⁆ ∈ ⁅E, M⁆ :=
        Subgroup.commutator_mem_commutator he (hσM x y hyx hyμ)
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    have hW6 : 6 ≤ Nat.card (Set.univ : Set α) := by
      rw [Nat.card_congr (Equiv.Set.univ α), Nat.card_eq_fintype_card]
      exact h6
    have hfixE : ∀ e ∈ E, ∀ x ∈ (Set.univ : Set α), e x = x ∨ e x = p.μ x := by
      intro e he
      exact fix_pairs_of_commute p (W := Set.univ) (fun x _ => Set.mem_univ _) hW6 (e := e)
        (fun x _ y _ hyx hyμ => hcommE e he x y hyx hyμ)
    have hfixE' : ∀ e ∈ E, ∀ x : α, e x = x := by
      intro e he x
      exact perfect_fix_pairs p (quasisimple_comm_eq hE.2.2) (W := Set.univ) hfixE
        (fun x _ => Set.mem_univ _) e he x (Set.mem_univ x)
    apply quasisimple_ne_bot hE.2.2
    rw [Subgroup.eq_bot_iff_forall]
    intro e he
    apply Equiv.ext
    intro x
    simpa using hfixE' e he x

theorem alt_le_of_primitive (p : FpfInv α) (h10 : 10 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) (hprim : MulAction.IsPreprimitive (↥Y) α) : alternatingGroup α ≤ Y := by
  obtain ⟨n, hn, x, hx⟩ := exists_bad_pair p (by omega) hprim
  obtain ⟨g, hg, h3⟩ := three_cycle_of_bad p h10 hB hn hx
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hg

theorem no_normal_three_group (p : FpfInv α) (h6 : 6 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {X : Subgroup (Perm α)} (hXY : X ≤ Y) (hn : (X.subgroupOf Y).Normal)
    (hX3 : IsPGroup 3 ↥X) (hne : X ≠ ⊥) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨σ, hσX⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hσ : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
  obtain ⟨z, hz⟩ : ∃ z, σ z ≠ z := by
    by_contra hcon
    push_neg at hcon
    exact hσ (Equiv.ext fun x => hcon x)
  have hblock : MulAction.IsBlock (↥Y) (MulAction.orbit (↥X) z) := orbit_isBlock hXY hn z
  obtain ⟨n, hn3⟩ : ∃ n : ℕ, Nat.card (MulAction.orbit (↥X) z) = 3 ^ n :=
    IsPGroup.card_orbit hX3 z
  have hzQ : z ∈ MulAction.orbit (↥X) z := MulAction.mem_orbit_self z
  have hσQ : σ z ∈ MulAction.orbit (↥X) z := MulAction.mem_orbit z (⟨σ, hσX⟩ : ↥X)
  have hpair : ∃ a ∈ MulAction.orbit (↥X) z, ∃ b ∈ MulAction.orbit (↥X) z, a ≠ b :=
    ⟨z, hzQ, σ z, hσQ, fun h => hz h.symm⟩
  have hclosed : ∀ x ∈ MulAction.orbit (↥X) z, p.μ x ∈ MulAction.orbit (↥X) z :=
    block_closed p h6 hB hblock hpair
  have heven : Even (Nat.card (MulAction.orbit (↥X) z)) := even_card_of_closed p _ hclosed
  rw [hn3] at heven
  exact absurd (Nat.even_pow.mp heven).1 (by decide)

theorem no_three_subnormal (p : FpfInv α) (h6 : 6 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hB : p.Contained Y) {K : Subgroup (Perm α)} (hKY : K ≤ Y) (hsub : IsSubnormal K Y)
    (h3 : Nat.card ↥K = 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKp : IsPGroup 3 ↥K := IsPGroup.of_card (n := 1) (by rw [h3, pow_one])
  have hKcore : K ≤ CFSG.Open.pCoreOf 3 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer hKp
  have hKY3 : K ≤ CFSG.Open.pCoreOf 3 Y :=
    hKcore.trans (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 3 hsub)
  have hXY : CFSG.Open.pCoreOf 3 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 3 Y
  have hXn : ((CFSG.Open.pCoreOf 3 Y).subgroupOf Y).Normal := by
    have heq : (CFSG.Open.pCoreOf 3 Y).subgroupOf Y = CFSG.pCore 3 ↥Y := by
      unfold CFSG.Open.pCoreOf
      exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
    rw [heq]
    exact CFSG.LieType.BorelTits.pCore_normal 3
  have hX3 : IsPGroup 3 ↥(CFSG.Open.pCoreOf 3 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 Y
  have hKbot : K ≠ ⊥ := by
    intro hK
    rw [hK, Subgroup.card_bot] at h3
    norm_num at h3
  have hne : CFSG.Open.pCoreOf 3 Y ≠ ⊥ := fun h => hKbot (le_bot_iff.mp (hKY3.trans h.le))
  exact no_normal_three_group p h6 hB hXY hXn hX3 hne

theorem fong_swap_pair_smul {p : FpfInv α} {S : Set α} (hS : ∀ t ∈ S, p.μ t ∈ S) (a : α) :
    swap a (p.μ a) • S = S := by
  have fwd : ∀ t ∈ S, swap a (p.μ a) t ∈ S := by
    intro t ht
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1
      exact hS _ ht
    · have ha : a = p.μ t := by rw [h2, p.inv]
      rw [ha]
      exact hS t ht
    · exact ht
  ext t
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact fwd s hs
  · intro ht
    refine ⟨swap a (p.μ a) t, fwd t ht, ?_⟩
    show swap a (p.μ a) (swap a (p.μ a) t) = t
    exact Equiv.swap_apply_self _ _ _

theorem fong_pair_pair_smul {p : FpfInv α} {S : Set α} (hS : ∀ t ∈ S, p.μ t ∈ S) (a b : α) :
    (swap a (p.μ a) * swap b (p.μ b)) • S = S := by
  rw [mul_smul, fong_swap_pair_smul hS b, fong_swap_pair_smul hS a]

theorem fong_smul_orbit_normClos {Y E : Subgroup (Perm α)} (x : α) {n : Perm α}
    (hn : n ∈ normClos Y E) :
    n • MulAction.orbit (↥(normClos Y E)) x = MulAction.orbit (↥(normClos Y E)) x :=
  MulAction.smul_orbit (⟨n, hn⟩ : ↥(normClos Y E)) x

theorem structure_component (p : FpfInv α) (h10 : 10 ≤ Fintype.card α) {Y : Subgroup (Perm α)}
    (hA : Y ≤ alternatingGroup α) (hB : p.Contained Y) {E : Subgroup (Perm α)}
    (hE : IsComponentOf E Y) :
    ∃ k, Even k ∧ 5 ≤ k ∧ k ≤ Fintype.card α ∧ Nonempty (↥E ≃* alternatingGroup (Fin k)) := by
  have hne : E ≠ ⊥ := quasisimple_ne_bot hE.2.2
  obtain ⟨e, heE, x, hex⟩ : ∃ e ∈ E, ∃ x : α, e x ≠ x := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext z
    simp [hcon g hg z]
  have hmove : ∃ e ∈ E, e x ≠ x := ⟨e, heE, hex⟩
  by_cases hNorb : MulAction.orbit (↥(normClos Y E)) x = Set.univ
  ·
    have hNt : MulAction.IsPretransitive ↥(normClos Y E) α :=
      (MulAction.isPretransitive_iff_orbit_eq_univ x).2 hNorb
    have hprim := primitive_of_normal_transitive p (by omega) hB hE hNt
    have hle := alt_le_of_primitive p h10 hB hprim
    have hYeq : Y = alternatingGroup α := le_antisymm hA hle
    have hEsub : CFSG.Open.IsSubnormal E (alternatingGroup α) := by
      rw [← hYeq]
      exact hE.2.1
    have hsimple : IsSimpleGroup ↥(alternatingGroup α) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; omega)
    have hEeq : E = alternatingGroup α := by
      rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hEsub hsimple with h | h
      · exact absurd h hne
      · exact h
    have heven : Even (Fintype.card α) := by
      have h := even_card_of_closed p Set.univ (fun _ _ => Set.mem_univ _)
      rwa [Nat.card_congr (Equiv.Set.univ α), Nat.card_eq_fintype_card] at h
    exact ⟨Fintype.card α, heven, by omega, le_refl _,
      ⟨(MulEquiv.subgroupCongr hEeq).trans (Equiv.altCongrHom (Fintype.equivFin α))⟩⟩
  ·
    have hblock : MulAction.IsBlock (↥Y) (MulAction.orbit (↥(normClos Y E)) x) :=
      orbit_isBlock (normClos_le Y E) (normClos_normal Y E) x
    have hxN : x ∈ MulAction.orbit (↥(normClos Y E)) x := MulAction.mem_orbit_self x
    have heN : e x ∈ MulAction.orbit (↥(normClos Y E)) x :=
      MulAction.mem_orbit_iff.2 ⟨⟨e, le_normClos hE.1 heE⟩, rfl⟩
    have hclosed : ∀ t ∈ MulAction.orbit (↥(normClos Y E)) x,
        p.μ t ∈ MulAction.orbit (↥(normClos Y E)) x :=
      block_closed p (by omega) hB hblock ⟨x, hxN, e x, heN, hex.symm⟩
    obtain ⟨Y₀, hY₀⟩ : ∃ Y₀ : Subgroup (Perm α),
        Y₀ = Y ⊓ MulAction.stabilizer (Perm α) (MulAction.orbit (↥(normClos Y E)) x) :=
      ⟨_, rfl⟩
    have hmemY₀ : ∀ σ : Perm α, σ ∈ Y₀ ↔
        (σ ∈ Y ∧ σ • MulAction.orbit (↥(normClos Y E)) x = MulAction.orbit (↥(normClos Y E)) x) := by
      intro σ
      rw [hY₀, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    have hEY₀ : E ≤ Y₀ := by
      intro g hg
      rw [hmemY₀]
      exact ⟨hE.1 hg, fong_smul_orbit_normClos x (le_normClos hE.1 hg)⟩
    have hY₀le : Y₀ ≤ Y := by
      intro σ hσ
      exact ((hmemY₀ σ).1 hσ).1
    have hB₀ : p.Contained Y₀ := by
      intro a b hba hbma
      rw [hmemY₀]
      exact ⟨hB a b hba hbma, fong_pair_pair_smul hclosed a b⟩
    have hsub₀ : CFSG.Open.IsSubnormal E Y₀ := by
      have h := CFSG.Quasithin.B113.isSubnormal_inf_of_le hE.2.1 hY₀le
      rwa [inf_eq_right.mpr hEY₀] at h
    have hE₀ : IsComponentOf E Y₀ := ⟨hEY₀, hsub₀, hE.2.2⟩
    have hY₀orb : MulAction.orbit (↥Y₀) x ≠ Set.univ := by
      intro huniv
      apply hNorb
      apply Set.eq_univ_of_forall
      intro t
      have ht : t ∈ MulAction.orbit (↥Y₀) x := by
        rw [huniv]
        exact Set.mem_univ t
      obtain ⟨σ, rfl⟩ := MulAction.mem_orbit_iff.1 ht
      have hσΓ : (σ : Perm α) • MulAction.orbit (↥(normClos Y E)) x
          = MulAction.orbit (↥(normClos Y E)) x := ((hmemY₀ (σ : Perm α)).1 σ.2).2
      have hmem : (σ : Perm α) • x ∈ (σ : Perm α) • MulAction.orbit (↥(normClos Y E)) x :=
        Set.smul_mem_smul_set hxN
      rw [hσΓ] at hmem
      exact hmem
    exact generic_component p (by omega) hB₀ hE₀ hmove hY₀orb

end CFSG.QuasithinUnique.L246C127.AltBig
