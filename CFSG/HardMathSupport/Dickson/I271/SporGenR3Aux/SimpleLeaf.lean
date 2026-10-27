module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Primitive
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Cover

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

section Simple

variable {Q : Type} [Group Q]

theorem isPGroup_inf_centralizer_of_normal_index {p : ℕ} {C : Subgroup Q} (E : Subgroup ↥C)
    [E.Normal] (hZ : Subgroup.center ↥(E.map C.subtype) = ⊥) (hq : IsPGroup p (↥C ⧸ E)) :
    IsPGroup p ↥(C ⊓ Subgroup.centralizer ((E.map C.subtype : Subgroup Q) : Set Q)) := by
  let L : Subgroup Q := E.map C.subtype
  let ι : ↥(C ⊓ Subgroup.centralizer (L : Set Q)) →* ↥C := Subgroup.inclusion inf_le_left
  let f : ↥(C ⊓ Subgroup.centralizer (L : Set Q)) →* ↥C ⧸ E := (QuotientGroup.mk' E).comp ι
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzE : ι z ∈ E := (QuotientGroup.eq_one_iff _).1 hz
    have hzL : (z : Q) ∈ L := ⟨ι z, hzE, rfl⟩
    let ζ : ↥L := ⟨(z : Q), hzL⟩
    have hζ : ζ ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro b
      have h1 : (b : Q) * (z : Q) = (z : Q) * (b : Q) :=
        Subgroup.mem_centralizer_iff.1 z.2.2 _ b.2
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hζ
    have h4 : (z : Q) = 1 := congrArg (fun x : ↥L => (x : Q)) hζ
    exact Subtype.ext h4
  exact hq.of_injective f hf

variable [Finite Q]

theorem glaPPrimeCore_eq_bot_of_simple {p : ℕ} (hp : p.Prime) {J : Type} [Group J] [Finite J]
    [IsSimpleGroup J] (hpJ : p ∣ Nat.card J) : GLAPPrimeCore p J = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p J)) :=
    CFSG.pPrimeCore_coprime_card (p := p) (G := J)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p J) with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hcop
    exact hp.ne_one (hcop.eq_one_of_dvd hpJ)

noncomputable def pQuotEquivSelf {p : ℕ} (L : Subgroup Q) (hcore : GLAPPrimeCore p ↥L = ⊥) :
    PQuot p L ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot

noncomputable def pSimpleEquivSelf {p : ℕ} (L : Subgroup Q) (hcore : GLAPPrimeCore p ↥L = ⊥)
    (hZ : Subgroup.center ↥L = ⊥) : PSimple p L ≃* ↥L :=
  (pSimpleEquivCenterQuot L hcore).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)

theorem center_eq_bot_of_simple_nonab {J : Type} [Group J] [IsSimpleGroup J]
    (hnab : ∃ a b : J, a * b ≠ b * a) : Subgroup.center J = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

theorem shapeRkAt_of_normal_pindex {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop} {t : Q}
    (E : Subgroup ↥(Subgroup.centralizer ({t} : Set Q))) [E.Normal]
    (hs : IsSimpleGroup ↥(E.map (Subgroup.centralizer ({t} : Set Q)).subtype))
    (hnab : ∃ a b : ↥(E.map (Subgroup.centralizer ({t} : Set Q)).subtype), a * b ≠ b * a)
    (hpL : p ∣ Nat.card ↥(E.map (Subgroup.centralizer ({t} : Set Q)).subtype))
    (hq : IsPGroup p (↥(Subgroup.centralizer ({t} : Set Q)) ⧸ E))
    (hG : Good (PSimple p (E.map (Subgroup.centralizer ({t} : Set Q)).subtype)))
    (hR : Rk (PQuot p (E.map (Subgroup.centralizer ({t} : Set Q)).subtype))) :
    ShapeRkAt p Good Rk t := by
  let L : Subgroup Q := E.map (Subgroup.centralizer ({t} : Set Q)).subtype
  have hLC : L ≤ Subgroup.centralizer ({t} : Set Q) := Subgroup.map_subtype_le E
  have hLn : ∀ g ∈ Subgroup.centralizer ({t} : Set Q), ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    rintro g hg _ ⟨e, he, rfl⟩
    exact ⟨⟨g, hg⟩ * e * ⟨g, hg⟩⁻¹, ‹E.Normal›.conj_mem e he ⟨g, hg⟩, rfl⟩
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_nonab hnab
  have hLq : CFSG.Open.IsQuasisimple ↥L := by
    refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h
  exact shapeRkAt_of_normal_quasisimple hp hLC hLn hLq hpL
    (isPGroup_inf_centralizer_of_normal_index E hZ hq) hG hR

end Simple

section Subtype

variable {G : Type} [Group G]

theorem map_centralizer_subtype' (P : Subgroup G) (x : ↥P) :
    (Subgroup.centralizer ({x} : Set ↥P)).map P.subtype =
      Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨congrArg Subtype.val hz, z.2⟩
  · rintro ⟨hy, hyP⟩
    exact ⟨⟨y, hyP⟩, Subtype.ext hy, rfl⟩

theorem shapeRkAt_of_subgroup_data {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (P : Subgroup G) [Finite P] (x : ↥P) (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P)
    (hLn : ∀ g ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    {k : ℕ} (hk : Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ P) = Nat.card ↥L * p ^ k)
    (hG : Good ↥L) (hR : Rk ↥L) : ShapeRkAt p Good Rk x := by
  have hLP : L ≤ P := fun l hl => (hLC hl).2
  haveI : Finite ↥L := Finite.of_injective (Subgroup.inclusion hLP) (Subgroup.inclusion_injective hLP)
  let C' : Subgroup ↥P := Subgroup.centralizer ({x} : Set ↥P)
  let L' : Subgroup ↥P := L.comap P.subtype
  have hmapC : C'.map P.subtype = Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
    exact map_centralizer_subtype' P x
  have hL'C : L' ≤ C' := by
    intro l hl
    have hl1 : (l : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P :=
      hLC hl
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
  have hsE : IsSimpleGroup ↥(E.map C'.subtype) := eE.isSimpleGroup_congr.2 hs
  have hnabE : ∃ a b : ↥(E.map C'.subtype), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eE.symm a, eE.symm b, fun h => hab (by simpa using congrArg eE h)⟩
  have hpE : p ∣ Nat.card ↥(E.map C'.subtype) := by
    rw [Nat.card_congr eE.toEquiv]; exact hpL
  have hq : IsPGroup p (↥C' ⧸ E) := by
    have hcardC : Nat.card ↥C' = Nat.card ↥L * p ^ k := by
      rw [← hk, ← hmapC, Subgroup.card_map_of_injective P.subtype_injective]
    have hcardE : Nat.card ↥E = Nat.card ↥L := by
      rw [← Subgroup.card_map_of_injective C'.subtype_injective, hEmap]
      exact Nat.card_congr eL.toEquiv
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup E
    haveI : Fact p.Prime := ⟨hp⟩
    refine IsPGroup.of_card (n := k) ?_
    have hpos : 0 < Nat.card ↥L := Nat.card_pos
    rw [hcardC, hcardE] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm (Nat.card ↥L) _, ← h1])
  have hZE : Subgroup.center ↥(E.map C'.subtype) = ⊥ := by
    haveI := hsE
    exact center_eq_bot_of_simple_nonab hnabE
  have hcoreE : GLAPPrimeCore p ↥(E.map C'.subtype) = ⊥ := by
    haveI := hsE
    exact glaPPrimeCore_eq_bot_of_simple hp hpE
  refine shapeRkAt_of_normal_pindex hp E hsE hnabE hpE hq ?_ ?_
  · exact hGood ↥L _ ((pSimpleEquivSelf (E.map C'.subtype) hcoreE hZE).trans eE).symm hG
  · exact hRk ↥L _ ((pQuotEquivSelf (E.map C'.subtype) hcoreE).trans eE).symm hR

end Subtype

section Constrained

variable {S T : Type} [Group S] [Group T]

theorem pConstrainedShape_of_normal_pgroup {p : ℕ} {C R : Subgroup S} (hRC : R ≤ C)
    (hn : (R.subgroupOf C).Normal) (hp : IsPGroup p ↥R)
    (hc : Subgroup.centralizer (R : Set S) ⊓ C ≤ R) : PConstrainedShape p C := by
  refine ⟨R, hRC, fun g hg q hq => ?_, hp, fun x hx => hc ⟨hx.2, hx.1⟩⟩
  have := hn.conj_mem ⟨q, hRC hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem pConstrainedShape_of_map_injective {p : ℕ} (f : S →* T) (hf : Function.Injective f)
    {C : Subgroup S} (h : PConstrainedShape p (C.map f)) : PConstrainedShape p C := by
  obtain ⟨Q, hQC, hQn, hQp, hQc⟩ := h
  let R : Subgroup S := (Q.comap f) ⊓ C
  have hRQ : R.map f = Q := by
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact hr.1
    · intro q hq
      obtain ⟨c, hc, rfl⟩ := hQC hq
      exact ⟨c, ⟨hq, hc⟩, rfl⟩
  refine ⟨R, inf_le_right, fun g hg r hr => ?_, ?_, fun x hx => ?_⟩
  · refine ⟨?_, C.mul_mem (C.mul_mem hg hr.2) (C.inv_mem hg)⟩
    have := hQn (f g) ⟨g, hg, rfl⟩ (f r) (hRQ ▸ ⟨r, hr, rfl⟩)
    simpa using this
  · exact hQp.of_equiv ((R.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hRQ)).symm
  · have hxC := hx.1
    have : f x ∈ Q := by
      refine hQc ⟨⟨x, hxC, rfl⟩, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      rw [← hRQ] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      have := Subgroup.mem_centralizer_iff.1 hx.2 r hr
      have h2 := congrArg f this
      simpa using h2
    exact ⟨this, hxC⟩

end Constrained

section Transfer

theorem ShapeRkAt.of_centralizer_eq {p : ℕ} {Good Rk : ∀ (T : Type) [Group T], Prop} {Q : Type}
    [Group Q] {k k' : Q} (h : Subgroup.centralizer ({k} : Set Q) = Subgroup.centralizer ({k'} : Set Q))
    (hk : ShapeRkAt p Good Rk k) : ShapeRkAt p Good Rk k' := by
  unfold ShapeRkAt at hk ⊢
  rw [← h]
  exact hk

theorem CentShape.of_centShapeRk {p : ℕ} {Good Rk : ∀ (T : Type) [Group T], Prop} {Q : Type}
    [Group Q] (h : CentShapeRk p Good Rk Q) : CentShape p Good Q := by
  intro k hk1 hkp
  rcases h k hk1 hkp with hc | ⟨J, hJ, hu, hG, -⟩
  · exact Or.inl hc
  · exact Or.inr ⟨J, hJ, hu, hG⟩

end Transfer

end CFSG.HardMathSupport.Dickson.I271
