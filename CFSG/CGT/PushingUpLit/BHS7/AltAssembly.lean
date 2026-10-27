module

public import CFSG.CGT.PushingUpLit.BHS7.AltCStar
public import CFSG.CGT.PushingUpLit.BHS7.AltPerm2

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement
open Equiv Equiv.Perm

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ} {m : ℕ}

theorem le_cStarIn_of_minCex (h : MinCex G T) : T ≤ cStarIn G T := by
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf h.sylow
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  have hT0 : T ≠ ⊥ := fun h0 => hb0 (le_bot_iff.mp ((inf_le_left : baum T ≤ T).trans h0.le))
  exact fun t ht => inf_normalizer_le_cStarIn hT2.2.1 hT0 ⟨hT2.1 ht, Subgroup.le_normalizer ht⟩

theorem AltAct.exists_cStarIn_iff (A : AltAct G T E m) (hm : 1 ≤ m) (hk : A.k = m)
    (h : MinCex G T) (hE : IsBTBlock G T E) (hS : IsSylowTwoOf (T ⊓ E) E)
    (hnot : ¬ E ≤ cStarIn G T) :
    ∃ p₀ : Fin (2 * m + 1), ∀ g : ↥(E ⊔ baum T), ((g : Γ) ∈ cStarIn G T ↔ A.Φ g p₀ = p₀) := by
  classical
  have hG := h.charTwo
  have hT : IsSylowOf 2 T G := h.sylow
  have hT2 : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hEG : E ≤ G := hE.le
  have hHG : E ⊔ baum T ≤ G := sup_le hEG ((inf_le_left : baum T ≤ T).trans hT2.1)
  have hSH : IsSylowTwoOf (T ⊓ (E ⊔ baum T)) (E ⊔ baum T) :=
    isSylowTwoOf_inf_sup_baum hT2.2.1 hBE hS
  have hTC : T ≤ cStarIn G T := le_cStarIn_of_minCex h
  have hker : ∀ x : ↥(E ⊔ baum T), A.Φ x = 1 → (x : Γ) ∈ cStarIn G T := by
    intro x hx
    have hc := (A.ker_iff x).mp hx
    exact hTC (inf_centralizer_le_of_isSylowTwoOf hG hT hE hSH ⟨x.2, hc⟩)
  have hY : IsMaxSwapGroup A.Y := by
    obtain ⟨T₀, h1, h2, h3, h4⟩ := A.baum_swap
    exact ⟨T₀, h1, h2, by rw [h3, hk]; omega, h4⟩
  obtain ⟨σ, p₀, hσ, hYσ⟩ := exists_isPairing_of_isMaxSwapGroup hY
  refine ⟨p₀, ?_⟩
  set M : Subgroup (Perm (Fin (2 * m + 1))) :=
    ((cStarIn G T).subgroupOf (E ⊔ baum T)).map A.Φ with hM
  have hMmem : ∀ g : ↥(E ⊔ baum T), A.Φ g ∈ M ↔ (g : Γ) ∈ cStarIn G T := by
    intro g
    constructor
    · rintro ⟨g', hg', hgg'⟩
      have hg'C : (g' : Γ) ∈ cStarIn G T := hg'
      have h1 : A.Φ (g'⁻¹ * g) = 1 := by rw [map_mul, map_inv, hgg', inv_mul_cancel]
      have h2 := hker _ h1
      have h3 : (g : Γ) = (g' : Γ) * ((g'⁻¹ * g : ↥(E ⊔ baum T)) : Γ) := by simp
      rw [h3]
      exact (cStarIn G T).mul_mem hg'C h2
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hCent : Cent σ ≤ M := by
    intro ν hν
    obtain ⟨g, rfl⟩ := A.surj ν
    rw [hMmem]
    refine A.mem_cStarIn_of_mem_normalizer h hE ?_
    have hnorm := cent_le_normalizer_closure hσ hν
    rw [← hYσ] at hnorm
    exact hnorm
  have hswaps : ∀ x y : Fin (2 * m + 1), x ≠ p₀ → y ≠ p₀ → y ≠ x → swap x y ∈ M := by
    by_cases hm1 : m = 1
    · intro x y hx hy hyx
      have := eq_sigma_of_three hσ (by omega : 2 * m + 1 = 3) hx hy hyx
      rw [this]
      exact hCent (swap_partner_mem_cent hσ x)
    · have hm2 : 2 ≤ m := by omega
      have hP2 : IsPGroup 2 ↥((T ⊓ (E ⊔ baum T)).subgroupOf (E ⊔ baum T)) :=
        hSH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH.1).symm
      set P : Subgroup (Perm (Fin (2 * m + 1))) :=
        ((T ⊓ (E ⊔ baum T)).subgroupOf (E ⊔ baum T)).map A.Φ with hP
      have hPsyl : IsSylowTwoOf P ⊤ := isSylowTwoOf_map_top A.Φ A.surj hP2 hSH.2.2
      have hYP : ∀ x, x ≠ p₀ → swap x (σ x) ∈ P := by
        intro x hx
        have hxY : swap x (σ x) ∈ A.Y := by
          rw [hYσ]
          exact Subgroup.subset_closure ⟨x, hx, rfl⟩
        obtain ⟨b, hb, hbx⟩ := hxY
        refine ⟨b, ?_, hbx⟩
        have hbB : (b : Γ) ∈ baum T := hb
        exact ⟨(inf_le_left : baum T ≤ T) hbB, b.2⟩
      have hPfix : ∀ s ∈ P, s p₀ = p₀ :=
        apply_p₀_of_isPGroup hσ (odd_two_mul_add_one m) (hPsyl.2.1) hYP
      obtain ⟨s, hs, x, hsx1, hsx2⟩ := exists_apply_notMem_pair hσ (by omega : 4 ≤ 2 * m + 1) hPsyl
      have hx : x ≠ p₀ := fun e => hsx1 (by rw [e, hPfix s hs])
      have hy : s x ≠ p₀ := fun e => hx (s.injective (e.trans (hPfix s hs).symm))
      have hsw : swap x (s x) ∈ M := by
        obtain ⟨g, hg⟩ := A.surj (swap x (s x))
        rw [← hg, hMmem]
        refine centralizer_le_cStarIn G T ⟨hHG g.2, ?_⟩
        refine A.mem_centralizer_of_fixes hm hG hT hE hS (g := g) fun u hu => ?_
        rw [hg]
        have hs' : coreAct (2 * m + 1) s u = u := by
          obtain ⟨t₀, ht₀, rfl⟩ := hs
          exact hu t₀ (Subgroup.mem_subgroupOf.mp ht₀).1
        exact coreAct_swap_eq_of_vcoord_eq u (vcoord_apply_eq_of_fixed u hs' x).symm
      intro x' y' hx' hy' hyx'
      exact swap_mem_of_cent_le hσ hCent hx hy hsx1 hsx2 hsw hx' hy' hyx'
  have hall : ∀ g : Perm (Fin (2 * m + 1)), g p₀ = p₀ → g ∈ M := fun g hg =>
    mem_of_fix_of_swaps_mem hswaps hg
  have hM1 : ∀ g ∈ M, g p₀ = p₀ := by
    intro g₁ hg₁
    by_contra hne
    have htop : M = ⊤ := eq_top_of_stabilizer_le (by omega : 2 ≤ 2 * m + 1) hall hg₁ hne
    apply hnot
    intro e he
    have heH : e ∈ E ⊔ baum T := (le_sup_left : E ≤ E ⊔ baum T) he
    have : A.Φ ⟨e, heH⟩ ∈ M := htop ▸ Subgroup.mem_top _
    exact (hMmem ⟨e, heH⟩).mp this
  intro g
  constructor
  · intro hg
    exact hM1 _ ((hMmem g).mpr hg)
  · intro hg
    exact (hMmem g).mp (hall _ hg)

theorem mulEquiv_map_mk'_of_ker {E' A' : Type*} [Group E'] [Group A'] (ψ : E' →* A')
    (N : Subgroup E') [N.Normal] (hN : ψ.ker = N) (K : Subgroup E') :
    Nonempty (↥(K.map (QuotientGroup.mk' N)) ≃* ↥(K.map ψ)) := by
  let ψ' : E' ⧸ N →* A' := QuotientGroup.lift N ψ hN.symm.le
  have hcomp : ψ'.comp (QuotientGroup.mk' N) = ψ := MonoidHom.ext fun x => rfl
  have hinj : Function.Injective ψ' := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H a =>
      have h1 : ψ a = 1 := hx
      have h2 : a ∈ N := hN ▸ (MonoidHom.mem_ker.mpr h1)
      exact (QuotientGroup.eq_one_iff a).mpr h2
  have hmap : (K.map (QuotientGroup.mk' N)).map ψ' = K.map ψ := by
    rw [Subgroup.map_map, hcomp]
  exact ⟨(Subgroup.equivMapOfInjective _ ψ' hinj).trans (MulEquiv.subgroupCongr hmap)⟩

omit [Finite Γ] in
theorem AltAct.nonempty_mulEquiv_cStarIn (A : AltAct G T E m) (hE : IsBTBlock G T E)
    (hchar : CharTwo E) {p₀ : Fin (2 * m + 1)}
    (hp₀ : ∀ g : ↥(E ⊔ baum T), ((g : Γ) ∈ cStarIn G T ↔ A.Φ g p₀ = p₀)) :
    Nonempty ((((cStarIn G T ⊓ E).subgroupOf E).map (QuotientGroup.mk' (pCore 2 ↥E))) ≃*
      alternatingGroup (Fin (2 * m))) := by
  classical
  have hWab := hE.elemAbelian.1
  let ψ : ↥E →* alternatingGroup (Fin (2 * m + 1)) :=
    (A.Φ.comp (Subgroup.inclusion (le_sup_left : E ≤ E ⊔ baum T))).codRestrict
      (alternatingGroup (Fin (2 * m + 1))) fun e => A.alt_of_mem _ e.2
  have hψ : ∀ e : ↥E, ((ψ e : alternatingGroup (Fin (2 * m + 1))) : Perm (Fin (2 * m + 1))) =
      A.Φ ⟨e, (le_sup_left : E ≤ E ⊔ baum T) e.2⟩ := fun e => rfl
  have hker : ψ.ker = pCore 2 ↥E := by
    rw [pCore_eq_inf_centralizer hchar hWab]
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro he
      refine ⟨e.2, (A.ker_iff ⟨e, (le_sup_left : E ≤ E ⊔ baum T) e.2⟩).mp ?_⟩
      exact congrArg Subtype.val he
    · rintro ⟨-, hc⟩
      exact Subtype.ext ((A.ker_iff ⟨e, (le_sup_left : E ≤ E ⊔ baum T) e.2⟩).mpr hc)
  have himage : ((cStarIn G T ⊓ E).subgroupOf E).map ψ = fixAlt p₀ := by
    ext a
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [mem_fixAlt, hψ]
      exact (hp₀ ⟨e, (le_sup_left : E ≤ E ⊔ baum T) e.2⟩).mp
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp he)).1
    · intro ha
      rw [mem_fixAlt] at ha
      obtain ⟨x, hxE, hxa⟩ := A.exists_of_alt a a.2
      refine ⟨⟨x, hxE⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
        ⟨(hp₀ x).mpr (by rw [hxa]; exact ha), hxE⟩), Subtype.ext (by rw [hψ]; exact hxa)⟩
  obtain ⟨e₁⟩ := mulEquiv_map_mk'_of_ker ψ (pCore 2 ↥E) hker ((cStarIn G T ⊓ E).subgroupOf E)
  obtain ⟨e₂⟩ := nonempty_mulEquiv_fixAlt p₀
  exact ⟨e₁.trans ((MulEquiv.subgroupCongr himage).trans e₂)⟩

theorem omegaCStarAlt_of_omegaMaxSwap (h : MinCex G T) (hms : OmegaMaxSwap G T) :
    OmegaCStarAlt G T := by
  intro E hE m hm hn
  have hEb : IsBTBlock G T E := omega_isBTBlock h hE
  have hS : IsSylowTwoOf (T ⊓ E) E :=
    isSylowTwoOf_inf_of_isSubnormal hE.2 (isSylowTwoOf_of_isSylowOf h.sylow)
  obtain ⟨A⟩ := nonempty_altAct h.charTwo h.sylow hEb hm hn
  have hk : A.k = m := by
    by_cases hm1 : m = 1
    · have h1 := A.one_le_k
      have h2 := A.k_le
      omega
    · have h2 : 2 ≤ m := by omega
      have h3 := hms E hE m h2 hn
      rw [A.card_baum] at h3
      exact Nat.pow_right_injective le_rfl h3
  obtain ⟨p₀, hp₀⟩ := A.exists_cStarIn_iff hm hk h hEb hS (omega_not_le_cStarIn h hE)
  exact A.nonempty_mulEquiv_cStarIn hEb (charTwo_of_isBTBlock h.charTwo h.sylow hEb) hp₀

end CFSG.CGT.PushingUpLit.BHS7
