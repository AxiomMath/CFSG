module

public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open Equiv Equiv.Perm CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {n : ℕ}

structure IsPairing (σ : Perm (Fin n)) (p₀ : Fin n) : Prop where
  mul_self : σ * σ = 1
  fixed : σ p₀ = p₀
  unique : ∀ x, σ x = x → x = p₀

namespace IsPairing

variable {σ : Perm (Fin n)} {p₀ : Fin n}

theorem sigma_sigma (h : IsPairing σ p₀) (x : Fin n) : σ (σ x) = x := by
  have := congrArg (fun f : Perm (Fin n) => f x) h.mul_self
  simpa using this

theorem sigma_ne_self (h : IsPairing σ p₀) {x : Fin n} (hx : x ≠ p₀) : σ x ≠ x :=
  fun e => hx (h.unique x e)

theorem sigma_ne_p₀ (h : IsPairing σ p₀) {x : Fin n} (hx : x ≠ p₀) : σ x ≠ p₀ := fun e => by
  have := h.sigma_sigma x
  rw [e, h.fixed] at this
  exact hx this.symm

end IsPairing

abbrev Cent (σ : Perm (Fin n)) : Subgroup (Perm (Fin n)) := Subgroup.centralizer {σ}

theorem mem_cent {σ ν : Perm (Fin n)} : ν ∈ Cent σ ↔ σ * ν = ν * σ := by
  rw [Subgroup.mem_centralizer_iff]
  simp

variable {σ : Perm (Fin n)} {p₀ : Fin n}

theorem apply_sigma_of_mem_cent {ν : Perm (Fin n)} (hν : ν ∈ Cent σ) (x : Fin n) :
    ν (σ x) = σ (ν x) := by
  have := congrArg (fun f : Perm (Fin n) => f x) (mem_cent.mp hν)
  simpa using this.symm

theorem swap_partner_mem_cent (h : IsPairing σ p₀) (c : Fin n) : swap c (σ c) ∈ Cent σ := by
  rw [mem_cent]
  have h1 := swap_apply_apply σ c (σ c)
  rw [h.sigma_sigma c, swap_comm] at h1
  calc σ * swap c (σ c) = (σ * swap c (σ c) * σ⁻¹) * σ := by group
    _ = swap c (σ c) * σ := by rw [← h1]

def rho (σ : Perm (Fin n)) (c d : Fin n) : Perm (Fin n) := swap c d * swap (σ c) (σ d)

theorem rho_mem_cent (h : IsPairing σ p₀) {c d : Fin n} (hc : c ≠ p₀) (hd : d ≠ p₀)
    (hcd : c ≠ d) (hd' : d ≠ σ c) : rho σ c d ∈ Cent σ := by
  rw [mem_cent]
  have hcσc := h.sigma_ne_self hc
  have hdσd := h.sigma_ne_self hd
  have hcσd : c ≠ σ d := fun e => hd' (by rw [e, h.sigma_sigma])
  have hσcσd : σ c ≠ σ d := fun e => hcd (σ.injective e)
  have hnd : [c, d, σ c, σ d].Nodup := by
    simp [hcd, hcσc.symm, hcσd, hd', hdσd.symm, hσcσd]
  have hdis : Disjoint (swap c d) (swap (σ c) (σ d)) := disjoint_swap_swap hnd
  have hcomm : swap c d * swap (σ c) (σ d) = swap (σ c) (σ d) * swap c d :=
    (hdis.commute).eq
  have e1 := swap_apply_apply σ c d
  have e2 := swap_apply_apply σ (σ c) (σ d)
  rw [h.sigma_sigma c, h.sigma_sigma d] at e2
  unfold rho
  calc σ * (swap c d * swap (σ c) (σ d))
      = (σ * swap c d * σ⁻¹) * (σ * swap (σ c) (σ d) * σ⁻¹) * σ := by group
    _ = swap (σ c) (σ d) * swap c d * σ := by rw [← e1, ← e2]
    _ = swap c d * swap (σ c) (σ d) * σ := by rw [hcomm]

theorem rho_apply_left (h : IsPairing σ p₀) {c d : Fin n} (hc : c ≠ p₀)
    (hd' : d ≠ σ c) : rho σ c d c = d := by
  have hcσc := h.sigma_ne_self hc
  have hcσd : c ≠ σ d := fun e => hd' (by rw [e, h.sigma_sigma])
  unfold rho
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hcσc.symm hcσd, swap_apply_left]

theorem rho_apply_of_notMem {c d x : Fin n} (hxc : x ≠ c) (hxd : x ≠ d) (hxσc : x ≠ σ c)
    (hxσd : x ≠ σ d) : rho σ c d x = x := by
  unfold rho
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxσc hxσd, swap_apply_of_ne_of_ne hxc hxd]

theorem exists_cent_apply_eq (h : IsPairing σ p₀) {a x : Fin n} (ha : a ≠ p₀) (hx : x ≠ p₀) :
    ∃ ν ∈ Cent σ, ν a = x := by
  by_cases hax : a = x
  · exact ⟨1, Subgroup.one_mem _, by simp [hax]⟩
  by_cases hax' : a = σ x
  · refine ⟨swap x (σ x), swap_partner_mem_cent h x, ?_⟩
    rw [hax', swap_apply_right]
  · refine ⟨rho σ a x, rho_mem_cent h ha hx hax ?_, rho_apply_left h ha ?_⟩
    · intro e
      exact hax' (by rw [e, h.sigma_sigma])
    · intro e
      exact hax' (by rw [e, h.sigma_sigma])

theorem apply_p₀_of_mem_cent (h : IsPairing σ p₀) {ν : Perm (Fin n)} (hν : ν ∈ Cent σ) :
    ν p₀ = p₀ := by
  apply h.unique
  rw [← apply_sigma_of_mem_cent hν, h.fixed]

theorem exists_cent_apply_eq₂ (h : IsPairing σ p₀) {a b x y : Fin n} (ha : a ≠ p₀) (hb : b ≠ p₀)
    (hx : x ≠ p₀) (hy : y ≠ p₀) (hba : b ≠ a) (hba' : b ≠ σ a) (hyx : y ≠ x) (hyx' : y ≠ σ x) :
    ∃ ν ∈ Cent σ, ν a = x ∧ ν b = y := by
  obtain ⟨ν₁, hν₁, h1⟩ := exists_cent_apply_eq h ha hx
  have hb₁ : ν₁ b ≠ x := fun e => hba (ν₁.injective (e.trans h1.symm))
  have hb₁' : ν₁ b ≠ σ x := fun e => hba' (ν₁.injective (by
    rw [e, apply_sigma_of_mem_cent hν₁, h1]))
  have hb₁p : ν₁ b ≠ p₀ := fun e => hb (ν₁.injective (e.trans (apply_p₀_of_mem_cent h hν₁).symm))
  by_cases hby : ν₁ b = y
  · exact ⟨ν₁, hν₁, h1, hby⟩
  by_cases hby' : ν₁ b = σ y
  · refine ⟨swap y (σ y) * ν₁, Subgroup.mul_mem _ (swap_partner_mem_cent h y) hν₁, ?_, ?_⟩
    · have hxy : x ≠ y := fun e => hyx e.symm
      have hxσy : x ≠ σ y := fun e => hyx' (by rw [e, h.sigma_sigma])
      rw [Perm.mul_apply, h1, swap_apply_of_ne_of_ne hxy hxσy]
    · rw [Perm.mul_apply, hby', swap_apply_right]
  · have hρ := rho_mem_cent h hb₁p hy hby (fun e => hby' (by rw [e, h.sigma_sigma]))
    refine ⟨rho σ (ν₁ b) y * ν₁, Subgroup.mul_mem _ hρ hν₁, ?_, ?_⟩
    · rw [Perm.mul_apply, h1]
      refine rho_apply_of_notMem hb₁.symm (fun e => hyx e.symm) ?_ ?_
      · intro e
        exact hb₁' (by rw [e, h.sigma_sigma])
      · intro e
        exact hyx' (by rw [e, h.sigma_sigma])
    · rw [Perm.mul_apply]
      exact rho_apply_left h hb₁p (fun e => hby' (by rw [e, h.sigma_sigma]))

theorem swap_mem_of_cent_le (h : IsPairing σ p₀) {M : Subgroup (Perm (Fin n))} (hM : Cent σ ≤ M)
    {a b : Fin n} (ha : a ≠ p₀) (hb : b ≠ p₀) (hba : b ≠ a) (hba' : b ≠ σ a)
    (hab : swap a b ∈ M) {x y : Fin n} (hx : x ≠ p₀) (hy : y ≠ p₀) (hyx : y ≠ x) :
    swap x y ∈ M := by
  by_cases hyx' : y = σ x
  · rw [hyx']
    exact hM (swap_partner_mem_cent h x)
  · obtain ⟨ν, hν, h1, h2⟩ := exists_cent_apply_eq₂ h ha hb hx hy hba hba' hyx hyx'
    have := M.mul_mem (M.mul_mem (hM hν) hab) (M.inv_mem (hM hν))
    rwa [← swap_apply_apply ν a b, h1, h2] at this

theorem mem_of_fix_of_swaps_mem {M : Subgroup (Perm (Fin n))}
    (hs : ∀ x y : Fin n, x ≠ p₀ → y ≠ p₀ → y ≠ x → swap x y ∈ M) {g : Perm (Fin n)}
    (hg : g p₀ = p₀) : g ∈ M := by
  classical
  have hgp : ∀ x, g x ≠ p₀ ↔ x ≠ p₀ := fun x => by
    constructor
    · intro hx e
      exact hx (by rw [e, hg])
    · intro hx e
      exact hx (g.injective (e.trans hg.symm))
  let g' : Perm {x : Fin n // x ≠ p₀} := g.subtypePerm hgp
  have hg' : g'.ofSubtype = g := by
    refine ofSubtype_subtypePerm hgp (fun x hx e => hx ?_)
    rw [e, hg]
  have hcl : Subgroup.closure {τ : Perm {x : Fin n // x ≠ p₀} | τ.IsSwap} ≤
      M.comap (ofSubtype : Perm {x : Fin n // x ≠ p₀} →* Perm (Fin n)) := by
    rw [Subgroup.closure_le]
    rintro τ ⟨u, v, huv, rfl⟩
    show ofSubtype (swap u v) ∈ M
    rw [ofSubtype_swap_eq]
    exact hs u v u.2 v.2 (fun e => huv (Subtype.ext e.symm))
  have htop : g' ∈ M.comap (ofSubtype : Perm {x : Fin n // x ≠ p₀} →* Perm (Fin n)) :=
    hcl (by rw [closure_isSwap]; exact Subgroup.mem_top _)
  rw [Subgroup.mem_comap, hg'] at htop
  exact htop

theorem eq_swap_apply_of_isSwap {α : Type*} [DecidableEq α] {t : Perm α} (ht : t.IsSwap) {x : α}
    (hx : t x ≠ x) : t = swap x (t x) := by
  obtain ⟨u, v, huv, rfl⟩ := ht
  by_cases hxu : x = u
  · subst hxu
    rw [swap_apply_left]
  · by_cases hxv : x = v
    · subst hxv
      rw [swap_apply_right, swap_comm]
    · exact absurd (swap_apply_of_ne_of_ne hxu hxv) hx

theorem exists_isPairing_of_isMaxSwapGroup {m : ℕ} {Y : Subgroup (Perm (Fin (2 * m + 1)))}
    (hY : CFSG.CGT.PushingUpLit.BHS.IsMaxSwapGroup Y) :
    ∃ (σ : Perm (Fin (2 * m + 1))) (p₀ : Fin (2 * m + 1)), IsPairing σ p₀ ∧
      Y = Subgroup.closure {t | ∃ x, x ≠ p₀ ∧ t = swap x (σ x)} := by
  classical
  obtain ⟨T₀, hsw, hcomm, hcard, rfl⟩ := hY
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hm] at hcard
  obtain ⟨σ, hσ, hσt⟩ := CFSG.CGT.PushingUpLit.BHS.exists_prod_swaps hsw hcomm
  rw [hcard] at hσt
  have hsupp : σ.support.card = 2 * m := by
    rw [← Equiv.Perm.sum_cycleType, hσt, Multiset.sum_replicate]
    simp [mul_comm]
  have hfix : (Finset.univ.filter fun x => σ x = x).card = 1 := by
    have h1 : (Finset.univ.filter fun x => σ x = x) = σ.supportᶜ := by
      ext x
      simp
    rw [h1, Finset.card_compl, hsupp]
    simp
  obtain ⟨p₀, hp₀⟩ := Finset.card_eq_one.mp hfix
  have hp₀fix : σ p₀ = p₀ := by
    have : p₀ ∈ (Finset.univ.filter fun x => σ x = x) := by rw [hp₀]; simp
    simpa using this
  have hunique : ∀ x, σ x = x → x = p₀ := fun x hx => by
    have : x ∈ (Finset.univ.filter fun x => σ x = x) := by simpa using hx
    rw [hp₀] at this
    simpa using this
  have hsq : σ * σ = 1 := by
    have h1 : orderOf σ ∣ 2 := by
      rw [← Equiv.Perm.lcm_cycleType, hσt]
      exact Multiset.lcm_dvd.mpr fun b hb => by
        rw [Multiset.eq_of_mem_replicate hb]
    have := orderOf_dvd_iff_pow_eq_one.mp h1
    simpa [pow_two] using this
  refine ⟨σ, p₀, ⟨hsq, hp₀fix, hunique⟩, ?_⟩
  congr 1
  ext t
  constructor
  · intro ht
    have hcf : t ∈ σ.cycleFactorsFinset := by rw [← Finset.mem_coe, hσ]; exact ht
    obtain ⟨-, hta⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcf
    obtain ⟨u, v, huv, rfl⟩ := hsw t ht
    have h1 : σ u = v := by
      have := hta u (by simp [Equiv.Perm.support_swap huv])
      rw [swap_apply_left] at this
      exact this.symm
    refine ⟨u, fun e => huv ?_, ?_⟩
    · rw [← h1, e, hp₀fix]
    · rw [h1]
  · rintro ⟨x, hx, rfl⟩
    have hxs : x ∈ σ.support := by
      rw [Equiv.Perm.mem_support]
      exact fun e => hx (hunique x e)
    have hcf : σ.cycleOf x ∈ σ.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hxs
    have hmem : σ.cycleOf x ∈ T₀ := by rw [← hσ]; exact hcf
    have hsw' := hsw _ hmem
    have hne : σ.cycleOf x x ≠ x := by
      rw [Equiv.Perm.cycleOf_apply_self]
      exact fun e => hx (hunique x e)
    have := eq_swap_apply_of_isSwap hsw' hne
    rw [Equiv.Perm.cycleOf_apply_self] at this
    rw [← this]
    exact hmem

theorem exists_mul_self_ne_one_of_isSylowTwoOf (hn : 4 ≤ n) {𝒮 : Subgroup (Perm (Fin n))}
    (h𝒮 : IsSylowTwoOf 𝒮 ⊤) : ∃ s ∈ 𝒮, s * s ≠ 1 := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  let d : Fin n := ⟨3, by omega⟩
  let l : List (Fin n) := [a, b, c, d]
  have hnd : l.Nodup := by simp [l, a, b, c, d, Fin.ext_iff]
  have hlen : 2 ≤ l.length := by simp [l]
  let ρ : Perm (Fin n) := l.formPerm
  have hcyc : ρ.IsCycle := List.isCycle_formPerm hnd hlen
  have hsupp : ρ.support.card = 4 := by
    rw [List.support_formPerm_of_nodup l hnd (fun x => by simp [l])]
    rw [List.toFinset_card_of_nodup hnd]
    simp [l]
  have hord : orderOf ρ = 4 := by rw [hcyc.orderOf, hsupp]
  have hsq : ρ * ρ ≠ 1 := fun e => by
    have h1 : orderOf ρ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    rw [hord] at h1
    omega
  have hX : IsPGroup 2 (Subgroup.zpowers ρ) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨S', hS', hXS'⟩ := B6.exists_isSylowTwoOf_ge hX (le_top : Subgroup.zpowers ρ ≤ ⊤)
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hS' h𝒮
  refine ⟨g * ρ * g⁻¹, ?_, fun e => hsq ?_⟩
  · rw [hg, B6.mem_conjSub]
    have : g⁻¹ * (g * ρ * g⁻¹) * g = ρ := by group
    rw [this]
    exact hXS' (Subgroup.mem_zpowers ρ)
  · have : g * (ρ * ρ) * g⁻¹ = 1 := by
      calc g * (ρ * ρ) * g⁻¹ = (g * ρ * g⁻¹) * (g * ρ * g⁻¹) := by group
        _ = 1 := e
    simpa using this

theorem exists_apply_notMem_pair (h : IsPairing σ p₀) (hn : 4 ≤ n) {𝒮 : Subgroup (Perm (Fin n))}
    (h𝒮 : IsSylowTwoOf 𝒮 ⊤) : ∃ s ∈ 𝒮, ∃ x, s x ≠ x ∧ s x ≠ σ x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hsq⟩ := exists_mul_self_ne_one_of_isSylowTwoOf hn h𝒮
  apply hsq
  refine Equiv.ext fun x => ?_
  simp only [Perm.mul_apply, Perm.one_apply]
  by_cases hx : s x = x
  · rw [hx, hx]
  · have h1 : s x = σ x := hcon s hs x hx
    by_cases hy : s (σ x) = σ x
    · have h3 : σ x = x := by
        apply s.injective
        rw [hy, h1]
      exact absurd (h1.trans h3) hx
    · have h2 : s (σ x) = σ (σ x) := hcon s hs (σ x) hy
      rw [h1, h2, h.sigma_sigma]

def fixAlt (p₀ : Fin n) : Subgroup (alternatingGroup (Fin n)) :=
  MulAction.stabilizer (alternatingGroup (Fin n)) ({p₀} : Set (Fin n))

theorem mem_fixAlt {p₀ : Fin n} {a : alternatingGroup (Fin n)} :
    a ∈ fixAlt p₀ ↔ (a : Perm (Fin n)) p₀ = p₀ := by
  unfold fixAlt
  rw [MulAction.mem_stabilizer_iff, Set.smul_set_singleton, Set.singleton_eq_singleton_iff]
  rfl

noncomputable def alternatingMulEquiv {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) : alternatingGroup α ≃* alternatingGroup β := by
  have h : (alternatingGroup α).map e.permCongrHom.toMonoidHom = alternatingGroup β := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_alternatingGroup] at hx ⊢
      show sign (e.permCongr x) = 1
      rw [sign_permCongr]
      exact hx
    · intro hg
      refine ⟨e.permCongrHom.symm g, ?_, e.permCongrHom.apply_symm_apply g⟩
      rw [mem_alternatingGroup] at hg ⊢
      have h1 : e.permCongrHom.symm g = e.symm.permCongr g := rfl
      rw [h1, sign_permCongr]
      exact hg
  exact (e.permCongrHom.subgroupMap (alternatingGroup α)).trans (MulEquiv.subgroupCongr h)

theorem nonempty_mulEquiv_fixAlt {m : ℕ} (p₀ : Fin (m + 1)) :
    Nonempty (↥(fixAlt p₀) ≃* alternatingGroup (Fin m)) := by
  classical
  let s : Finset (Fin (m + 1)) := Finset.univ.erase p₀
  have hcard : Fintype.card ↥s = m := by simp [s]
  let ε : ↥s ≃ Fin m := Fintype.equivFinOfCardEq hcard
  have hr : (alternatingGroup.ofSubtype s).range = fixAlt p₀ := by
    ext k
    rw [alternatingGroup.mem_range_ofSubtype_iff, mem_fixAlt]
    constructor
    · intro hk
      by_contra hne
      exact (by simp [s] : p₀ ∉ s) (hk (Perm.mem_support.mpr hne))
    · intro hk x hx
      have hxne : x ≠ p₀ := fun e => (Perm.mem_support.mp hx) (by rw [e]; exact hk)
      simp [s, hxne]
  exact ⟨(MulEquiv.subgroupCongr hr.symm).trans
    ((MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).symm.trans
      (alternatingMulEquiv ε))⟩

open CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin.G6 in
theorem vcoord_apply_eq_of_fixed (u : ↥(coreMod n)) {s : Perm (Fin n)}
    (hs : coreAct n s u = u) (i : Fin n) : vcoord u (s i) = vcoord u i := by
  have h := vcoord_coreAct s u (s i)
  rw [hs] at h
  simpa using h

open CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin.G6 in
theorem eq_one_of_fixed_alternatingGroup (hn : Odd n) (h3 : 3 ≤ n) {u : ↥(coreMod n)}
    (hu : ∀ a ∈ alternatingGroup (Fin n), coreAct n a u = u) : u = 1 := by
  classical
  have hn0 : 0 < n := by omega
  let i₀ : Fin n := ⟨0, hn0⟩
  have hconst : ∀ j, vcoord u j = vcoord u i₀ := by
    intro j
    by_cases hj : j = i₀
    · rw [hj]
    · have hcard : ({i₀, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
        have h2 : ({i₀, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      have hi₀j : i₀ ≠ j := fun h => hj h.symm
      have hjk : j ≠ k := fun h => hk.2 h.symm
      have hi₀k : i₀ ≠ k := fun h => hk.1 h.symm
      have ha : swap i₀ j * swap j k ∈ alternatingGroup (Fin n) := by
        rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hi₀j, Perm.sign_swap hjk]
        decide
      have h1 := vcoord_apply_eq_of_fixed u (hu _ ha) i₀
      have h2 : (swap i₀ j * swap j k) i₀ = j := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hi₀j hi₀k, swap_apply_left]
      rwa [h2] at h1
  have hsum := sum_vcoord u
  rw [Finset.sum_congr rfl (fun j _ => hconst j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hodd : ((n : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hn
  rw [hodd, one_mul] at hsum
  exact vcoord_ext fun i => by rw [hconst i, hsum]; rfl

end CFSG.CGT.PushingUpLit.BHS7
