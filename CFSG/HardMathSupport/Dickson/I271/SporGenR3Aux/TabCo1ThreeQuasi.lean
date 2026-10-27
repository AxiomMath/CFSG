module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzU43

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.Multipliers.U43

section Quasi

theorem shapeRkAt_of_subgroup_data_quasi {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (P : Subgroup G) [Finite P] (x : ↥P) (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P)
    (hLn : ∀ g ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hpL : p ∣ Nat.card ↥L)
    (hZp : IsPGroup p ↥(Subgroup.center ↥L))
    (hcent : ∀ c ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P, (∀ l ∈ L, l * c = c * l) →
      c ^ p = 1)
    (hG : Good (↥L ⧸ Subgroup.center ↥L)) (hR : Rk ↥L) : ShapeRkAt p Good Rk x := by
  have hLP : L ≤ P := fun l hl => (hLC hl).2
  haveI : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion hLP) (Subgroup.inclusion_injective hLP)
  let C' : Subgroup ↥P := Subgroup.centralizer ({x} : Set ↥P)
  let L' : Subgroup ↥P := L.comap P.subtype
  have hmapC : C'.map P.subtype = Subgroup.centralizer ({(x : G)} : Set G) ⊓ P :=
    map_centralizer_subtype' P x
  have hL'C : L' ≤ C' := by
    intro l hl
    have hl1 : (l : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := hLC hl
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hl1).1
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hc)
  let E : Subgroup ↥C' := L'.subgroupOf C'
  have hEn : E.Normal := by
    refine ⟨fun e he g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at he ⊢
    have hgC : ((g : ↥P) : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
      rw [← hmapC]
      exact ⟨g, g.2, rfl⟩
    have := hLn _ hgC _ he
    exact this
  haveI := hEn
  have hEmap : E.map C'.subtype = L' := Subgroup.map_subgroupOf_eq_of_le hL'C
  have eL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLP
  have eE : ↥(E.map C'.subtype) ≃* ↥L := (MulEquiv.subgroupCongr hEmap).trans eL
  have hqE : CFSG.Open.IsQuasisimple ↥(E.map C'.subtype) :=
    isQuasisimple_of_mulEquiv' eE.symm hq
  have hpE : p ∣ Nat.card ↥(E.map C'.subtype) := by
    rw [Nat.card_congr eE.toEquiv]; exact hpL
  have ecE : ↥(Subgroup.center ↥(E.map C'.subtype)) ≃* ↥(Subgroup.center ↥L) :=
    ((Subgroup.center ↥(E.map C'.subtype)).equivMapOfInjective eE.toMonoidHom eE.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_center_eq eE))
  have hZpE : IsPGroup p ↥(Subgroup.center ↥(E.map C'.subtype)) := hZp.of_equiv ecE.symm
  have hLn0 : ∀ g ∈ E.map C'.subtype, ∀ l ∈ E.map C'.subtype, g * l * g⁻¹ ∈ E.map C'.subtype :=
    fun g hg l hl => (E.map C'.subtype).mul_mem ((E.map C'.subtype).mul_mem hg hl)
      ((E.map C'.subtype).inv_mem hg)
  have hcoreE : GLAPPrimeCore p ↥(E.map C'.subtype) = ⊥ :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple hp le_rfl hLn0 hqE hpE
      (isPGroup_inf_centralizer_self _ hZpE)
  have hLC' : E.map C'.subtype ≤ Subgroup.centralizer ({x} : Set ↥P) := Subgroup.map_subtype_le E
  have hLn' : ∀ g ∈ Subgroup.centralizer ({x} : Set ↥P), ∀ l ∈ E.map C'.subtype,
      g * l * g⁻¹ ∈ E.map C'.subtype := by
    rintro g hg _ ⟨e, he, rfl⟩
    exact ⟨⟨g, hg⟩ * e * ⟨g, hg⟩⁻¹, hEn.conj_mem e he ⟨g, hg⟩, rfl⟩
  have hcentP : IsPGroup p ↥(Subgroup.centralizer ({x} : Set ↥P) ⊓
      Subgroup.centralizer ((E.map C'.subtype : Subgroup ↥P) : Set ↥P)) := by
    intro c
    refine ⟨1, ?_⟩
    have hcP : ((c : ↥P) : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
      rw [← hmapC]
      exact ⟨c.1, (Subgroup.mem_inf.1 c.2).1, rfl⟩
    have hcomm : ∀ l ∈ L, l * ((c : ↥P) : G) = ((c : ↥P) : G) * l := by
      intro l hl
      have hlE : (⟨l, hLP hl⟩ : ↥P) ∈ E.map C'.subtype := by
        rw [hEmap]
        exact hl
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 c.2).2 _ hlE
      exact congrArg Subtype.val this
    have h0 := hcent _ hcP hcomm
    have h1 : (c : ↥P) ^ p = 1 := Subtype.ext (by simpa using h0)
    have h2 : c ^ p = 1 := Subtype.ext h1
    rw [pow_one]
    exact h2
  have eq : (↥L ⧸ Subgroup.center ↥L) ≃*
      (↥(E.map C'.subtype) ⧸ Subgroup.center ↥(E.map C'.subtype)) :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥(E.map C'.subtype)) eE.symm
      (Subgroup.map_center_eq eE.symm)
  exact shapeRkAt_of_normal_quasisimple hp hLC' hLn' hqE hpE hcentP
    (hGood _ _ (eq.trans (pSimpleEquivCenterQuot (E.map C'.subtype) hcoreE).symm) hG)
    (hRk _ _ (eE.symm.trans (pQuotEquivSelf (E.map C'.subtype) hcoreE).symm) hR)

end Quasi

section Good

theorem goodSpor_three_of_equiv_X₀ {T : Type} [Group T]
    (e : T ≃* X₀) :
    GoodSpor 3 [.Suz] T :=
  Or.inl (leafType_three_of_equiv_X₀' e)

theorem goodSpor_three_alt9 : GoodSpor 3 [.Suz] ↥(alternatingGroup (Fin 9)) :=
  Or.inl (Or.inr ⟨9, by norm_num, by norm_num, by norm_num, ⟨MulEquiv.refl _⟩⟩)

theorem rkSpor_Suz_of_card_ne
    (b : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group))
    {T : Type} [Group T] (h6 : Nat.card (T ⧸ Subgroup.center T) ≠ 360)
    (hS : Nat.card (T ⧸ Subgroup.center T) ≠ 448345497600) : RkSpor 3 [.Suz] T := by
  rintro (⟨-, ⟨f⟩⟩ | ⟨S, hS', ⟨f⟩⟩)
  · exfalso
    apply h6
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  · simp only [List.mem_singleton] at hS'
    subst hS'
    obtain ⟨b'⟩ := b
    exfalso
    apply hS
    rw [Nat.card_congr (f.trans b'.symm).toEquiv]
    exact CFSG.Sporadic.Suz.card_Suz

theorem rkSpor_Suz_of_equiv_X₀
    (b : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group))
    {T : Type} [Group T] (e : (T ⧸ Subgroup.center T) ≃* X₀) : RkSpor 3 [.Suz] T := by
  have hcard : Nat.card (T ⧸ Subgroup.center T) = 3265920 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_X₀
  exact rkSpor_Suz_of_card_ne b (by omega) (by omega)

theorem alt9_noncomm : ∃ a c : ↥(alternatingGroup (Fin 9)), a * c ≠ c * a := by
  by_contra hcon
  push Not at hcon
  have hx : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 9) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have hy : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 9) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have h2 := congrArg Subtype.val (hcon ⟨_, hx⟩ ⟨_, hy⟩)
  have h3 : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 1 2) *
        (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 2 3) ≠
      (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 2 3) *
        (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 1 2) := by decide
  exact h3 h2

theorem card_alt9 : Nat.card ↥(alternatingGroup (Fin 9)) = 181440 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem alt9_subgroup_data {G : Type} [Group G] {L : Subgroup G}
    (e : ↥(alternatingGroup (Fin 9)) ≃* ↥L) :
    IsSimpleGroup ↥L ∧ (∃ a b : ↥L, a * b ≠ b * a) ∧ Nat.card ↥L = 181440 := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨e.symm.isSimpleGroup, ?_, ?_⟩
  · obtain ⟨a, c, hac⟩ := alt9_noncomm
    exact ⟨e a, e c, fun h => hac (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  · rw [← Nat.card_congr e.toEquiv, card_alt9]

theorem rkSpor_Suz_alt9
    (b : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group)) :
    RkSpor 3 [.Suz] ↥(alternatingGroup (Fin 9)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  have hZ : Subgroup.center ↥(alternatingGroup (Fin 9)) = ⊥ :=
    center_eq_bot_of_simple_nonab alt9_noncomm
  have hcard : Nat.card (↥(alternatingGroup (Fin 9)) ⧸
      Subgroup.center ↥(alternatingGroup (Fin 9))) = 181440 := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, card_alt9]
  exact rkSpor_Suz_of_card_ne b (by omega) (by omega)

end Good

end CFSG.HardMathSupport.Dickson.I271
