module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.GroupTheory

open scoped Pointwise

open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

@[expose] def IsRadicalPGroup (p : ℕ) (G₀ Q : Subgroup G) : Prop :=
  CFSG.Open.pCoreOf p (G₀ ⊓ Subgroup.normalizer (Q : Set G)) = Q

@[expose] def oppositePRadicals (p : ℕ) (G₀ Q : Subgroup G) : Set (Subgroup G) :=
  {V | IsRadicalPGroup p G₀ V ∧ Nat.card V = Nat.card Q ∧
    V ⊓ (G₀ ⊓ Subgroup.normalizer (Q : Set G)) = ⊥}

theorem pCoreOf_map_of_injective {X Y : Type*} [Group X] [Group Y] (p : ℕ) (f : X →* Y)
    (hf : Function.Injective f) (H : Subgroup X) :
    CFSG.Open.pCoreOf p (H.map f) = (CFSG.Open.pCoreOf p H).map f := by
  let e : H ≃* H.map f := H.equivMapOfInjective f hf
  have hcore : (CFSG.pCore p H).map e.toMonoidHom = CFSG.pCore p (H.map f) :=
    CFSG.pCore_map_iso p e
  have hcomp : (H.map f).subtype.comp e.toMonoidHom = f.comp H.subtype := by
    ext x
    exact Subgroup.coe_equivMapOfInjective_apply H f hf x
  unfold CFSG.Open.pCoreOf
  rw [← hcore, Subgroup.map_map, Subgroup.map_map, hcomp]

namespace IsRadicalPGroup

theorem le {p : ℕ} {G₀ Q : Subgroup G} (h : IsRadicalPGroup p G₀ Q) : Q ≤ G₀ :=
  calc Q = CFSG.Open.pCoreOf p (G₀ ⊓ Subgroup.normalizer (Q : Set G)) := h.symm
    _ ≤ G₀ ⊓ Subgroup.normalizer (Q : Set G) := pCoreOf_le p _
    _ ≤ G₀ := inf_le_left

theorem isPGroup {p : ℕ} [Fact p.Prime] {G₀ Q : Subgroup G} (h : IsRadicalPGroup p G₀ Q) :
    IsPGroup p Q := by
  rw [← h]
  exact (CFSG.pCore_isPGroup (p := p)
    (G := ↥(G₀ ⊓ Subgroup.normalizer (Q : Set G)))).map
    (G₀ ⊓ Subgroup.normalizer (Q : Set G)).subtype

theorem map_mulAut {p : ℕ} {G₀ Q : Subgroup G} (h : IsRadicalPGroup p G₀ Q) (e : MulAut G)
    (he : G₀.map e.toMonoidHom = G₀) :
    IsRadicalPGroup p G₀ (Q.map e.toMonoidHom) := by
  have hN : (Subgroup.normalizer (Q.map e.toMonoidHom) : Subgroup G) =
      (Subgroup.normalizer (Q : Set G)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq Q e).symm
  unfold IsRadicalPGroup at h ⊢
  rw [hN, ← he,
    ← Subgroup.map_inf_eq G₀ (Subgroup.normalizer (Q : Set G)) e.toMonoidHom e.injective,
    pCoreOf_map_mulEquiv p e (G₀ ⊓ Subgroup.normalizer (Q : Set G)), h]

theorem eq_of_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] {G₀ Q P : Subgroup G}
    (hQ : IsRadicalPGroup p G₀ Q) (hPG₀ : P ≤ G₀)
    (hNP : G₀ ⊓ Subgroup.normalizer (Q : Set G) ≤ P)
    (hQP : Q ≤ CFSG.Open.pCoreOf p P) :
    CFSG.Open.pCoreOf p P = Q ∧ G₀ ⊓ Subgroup.normalizer (Q : Set G) = P := by
  have hRp : IsPGroup p (CFSG.Open.pCoreOf p P) := pCoreOf_isPGroup p P
  have hPR : P ≤ Subgroup.normalizer (CFSG.Open.pCoreOf p P : Set G) := le_normalizer_pCoreOf p P
  have hNRQ : CFSG.Open.pCoreOf p P ⊓ Subgroup.normalizer (Q : Set G) ≤ Q :=
    calc CFSG.Open.pCoreOf p P ⊓ Subgroup.normalizer (Q : Set G)
        ≤ CFSG.Open.pCoreOf p (G₀ ⊓ Subgroup.normalizer (Q : Set G)) :=
          le_pCoreOf_of_le_normalizer p (inf_le_inf_right _ ((pCoreOf_le p P).trans hPG₀))
            (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
              ⟨hPR (hNP hg), Subgroup.le_normalizer hg.2⟩)
            (hRp.to_le inf_le_left)
      _ = Q := hQ
  have hQR : Q = CFSG.Open.pCoreOf p P := by
    by_contra hne
    exact lt_irrefl Q
      ((CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hRp (lt_of_le_of_ne hQP hne)).trans_le
        hNRQ)
  refine ⟨hQR.symm, le_antisymm hNP fun g hg => ⟨hPG₀ hg, ?_⟩⟩
  rw [hQR]
  exact hPR hg

end IsRadicalPGroup

theorem mem_oppositePRadicals_map_mulAut {p : ℕ} {G₀ Q V : Subgroup G}
    (hV : V ∈ oppositePRadicals p G₀ Q) (e : MulAut G) (he : G₀.map e.toMonoidHom = G₀) :
    V.map e.toMonoidHom ∈ oppositePRadicals p G₀ (Q.map e.toMonoidHom) := by
  obtain ⟨hrad, hcard, hinf⟩ := hV
  have hN : (Subgroup.normalizer (Q.map e.toMonoidHom) : Subgroup G) =
      (Subgroup.normalizer (Q : Set G)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq Q e).symm
  refine ⟨hrad.map_mulAut e he, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hcard,
      Subgroup.card_map_of_injective e.injective]
  · rw [hN, ← he,
      ← Subgroup.map_inf_eq G₀ (Subgroup.normalizer (Q : Set G)) e.toMonoidHom e.injective,
      ← Subgroup.map_inf_eq V (G₀ ⊓ Subgroup.normalizer (Q : Set G)) e.toMonoidHom e.injective,
      hinf, Subgroup.map_bot]

theorem mem_oppositePRadicals_map_conj {p : ℕ} {G₀ Q V : Subgroup G}
    (hV : V ∈ oppositePRadicals p G₀ Q) {g : G} (hg : g ∈ Subgroup.normalizer (G₀ : Set G)) :
    V.map (MulAut.conj g).toMonoidHom ∈
      oppositePRadicals p G₀ (Q.map (MulAut.conj g).toMonoidHom) := by
  exact mem_oppositePRadicals_map_mulAut hV (MulAut.conj g)
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)

@[expose] def HasGoodOppositePRadicals (p : ℕ) (G₀ Q : Subgroup G) : Prop :=
  ∃ V₀ ∈ oppositePRadicals p G₀ Q, Q ⊔ V₀ = G₀ ∧
    ∀ V ∈ oppositePRadicals p G₀ Q, ∃ u ∈ Q, V = V₀.map (MulAut.conj u).toMonoidHom

theorem HasGoodOppositePRadicals.map_mulAut {p : ℕ} {G₀ Q : Subgroup G}
    (h : HasGoodOppositePRadicals p G₀ Q) (e : MulAut G) (he : G₀.map e.toMonoidHom = G₀) :
    HasGoodOppositePRadicals p G₀ (Q.map e.toMonoidHom) := by
  obtain ⟨V₀, hV₀, hgen, hconj⟩ := h
  have hcomp : (e.toMonoidHom.comp e.symm.toMonoidHom) = MonoidHom.id G := by
    ext x; simp
  have hcomp' : (e.symm.toMonoidHom.comp e.toMonoidHom) = MonoidHom.id G := by
    ext x; simp
  have he' : G₀.map e.symm.toMonoidHom = G₀ := by
    rw [← he, Subgroup.map_map, hcomp', Subgroup.map_id]
    exact he.symm
  refine ⟨V₀.map e.toMonoidHom, mem_oppositePRadicals_map_mulAut hV₀ e he, ?_,
    fun V hV => ?_⟩
  · rw [← Subgroup.map_sup, hgen, he]
  · have hV' := mem_oppositePRadicals_map_mulAut hV e.symm he'
    rw [Subgroup.map_map, hcomp', Subgroup.map_id] at hV'
    obtain ⟨u, hu, huV⟩ := hconj _ hV'
    refine ⟨e u, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩, ?_⟩
    calc V = (V.map e.symm.toMonoidHom).map e.toMonoidHom := by
          rw [Subgroup.map_map, hcomp, Subgroup.map_id]
      _ = (V₀.map (MulAut.conj u).toMonoidHom).map e.toMonoidHom := by rw [huV]
      _ = (V₀.map e.toMonoidHom).map (MulAut.conj (e u)).toMonoidHom := by
          rw [Subgroup.map_map, Subgroup.map_map]
          congr 1
          ext x
          simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
            MulAut.conj_apply, map_mul, map_inv]

theorem HasGoodOppositePRadicals.map_conj {p : ℕ} {G₀ Q : Subgroup G}
    (h : HasGoodOppositePRadicals p G₀ Q) {g : G}
    (hg : g ∈ Subgroup.normalizer (G₀ : Set G)) :
    HasGoodOppositePRadicals p G₀ (Q.map (MulAut.conj g).toMonoidHom) := by
  exact h.map_mulAut (MulAut.conj g) (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)

theorem mem_oppositePRadicals_map_conj_of_mem {p : ℕ} {G₀ Q V : Subgroup G}
    (hV : V ∈ oppositePRadicals p G₀ Q) (hQG : Q ≤ G₀) {q : G} (hq : q ∈ Q) :
    V.map (MulAut.conj q).toMonoidHom ∈ oppositePRadicals p G₀ Q := by
  have hqN : q ∈ Subgroup.normalizer (G₀ : Set G) := Subgroup.le_normalizer (hQG hq)
  have hQQ : Q.map (MulAut.conj q).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hq)
  have := mem_oppositePRadicals_map_conj hV hqN
  rwa [hQQ] at this

theorem HasGoodOppositePRadicals.odd_card [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G₀ Q : Subgroup G} (h : HasGoodOppositePRadicals p G₀ Q) :
    Odd (Nat.card (oppositePRadicals p G₀ Q)) := by
  classical
  obtain ⟨V₀, hV₀, hgen, hconj⟩ := h
  have hQG : Q ≤ G₀ := hgen ▸ le_sup_left
  have hpQ : IsPGroup p Q := by
    obtain ⟨k, hk⟩ := hV₀.1.isPGroup.exists_card_eq
    exact IsPGroup.of_card (hV₀.2.1.symm.trans hk)
  let : MulAction Q (Subgroup G) :=
    MulAction.compHom (Subgroup G) (ConjAct.toConjAct.toMonoidHom.comp Q.subtype)
  have hsmul : ∀ (q : Q) (V : Subgroup G),
      q • V = V.map (MulAut.conj (q : G)).toMonoidHom := by
    intro q V
    rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have horbit : oppositePRadicals p G₀ Q = MulAction.orbit Q V₀ := by
    ext V
    constructor
    · intro hV
      obtain ⟨u, hu, rfl⟩ := hconj V hV
      exact ⟨⟨u, hu⟩, hsmul ⟨u, hu⟩ V₀⟩
    · rintro ⟨⟨u, hu⟩, rfl⟩
      show (⟨u, hu⟩ : Q) • V₀ ∈ oppositePRadicals p G₀ Q
      rw [hsmul]
      exact mem_oppositePRadicals_map_conj_of_mem hV₀ hQG hu
  have hdvd : Nat.card (oppositePRadicals p G₀ Q) ∣ Nat.card Q := by
    rw [horbit]
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Q V₀)
    rw [Nat.card_prod] at h
    exact ⟨Nat.card (MulAction.stabilizer Q V₀), h.symm⟩
  obtain ⟨k, hk⟩ := hpQ.exists_card_eq
  have hoddQ : Odd (Nat.card Q) := by
    rw [hk]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  exact Odd.of_dvd_nat hoddQ hdvd

theorem HasGoodOppositePRadicals.exists_fixed_of_twoGroup [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {G₀ Q : Subgroup G} (h : HasGoodOppositePRadicals p G₀ Q)
    (E : Subgroup (MulAut G)) (hE : IsPGroup 2 E)
    (hEG₀ : ∀ e ∈ E, G₀.map e.toMonoidHom = G₀)
    (hEQ : ∀ e ∈ E, Q.map e.toMonoidHom = Q) :
    ∃ V ∈ oppositePRadicals p G₀ Q, ∀ e ∈ E, V.map e.toMonoidHom = V := by
  classical
  have hodd : Odd (Nat.card (oppositePRadicals p G₀ Q)) := h.odd_card hp2
  let Opp := oppositePRadicals p G₀ Q
  let : MulAction E (Subgroup G) := MulAction.compHom (Subgroup G) E.subtype
  have hsmul : ∀ (e : E) (V : Subgroup G),
      e • V = V.map (e : MulAut G).toMonoidHom := by
    intro e V
    rw [MulAction.compHom_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hOpp : ∀ (e : E) {V : Subgroup G}, V ∈ Opp → e • V ∈ Opp := by
    intro e V hV
    have hmem := mem_oppositePRadicals_map_mulAut hV (e : MulAut G) (hEG₀ e e.2)
    rwa [hEQ e e.2] at hmem
  let : MulAction E ↥Opp :=
    { smul := fun e V => ⟨e • V.1, hOpp e V.2⟩
      one_smul := fun V => Subtype.ext (one_smul E V.1)
      mul_smul := fun a b V => Subtype.ext (mul_smul a b V.1) }
  obtain ⟨V, hV⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (↥Opp)
    hodd.not_two_dvd_nat
  refine ⟨V.1, V.2, fun e he => ?_⟩
  have hfix := hV ⟨e, he⟩
  have hfix' : (⟨e, he⟩ : E) • V.1 = V.1 := congrArg Subtype.val hfix
  rw [hsmul ⟨e, he⟩ V.1] at hfix'
  exact hfix'

section SubtypeTransport

variable {X : Type*} [Group X] (C : Subgroup X)

theorem map_subtype_normalizer_eq (S : Subgroup C) :
    (Subgroup.normalizer (S : Set C)).map C.subtype =
      C ⊓ Subgroup.normalizer (S.map C.subtype : Set X) := by
  have hS : (S.map C.subtype).subgroupOf C = S :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective S
  have h := Subgroup.subgroupOf_normalizer_eq (H := S.map C.subtype) (N := C)
    (Subgroup.map_subtype_le S)
  rw [hS] at h
  rw [← h, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem pCoreOf_map_subtype_normalizer (p : ℕ) (S : Subgroup C) :
    (CFSG.Open.pCoreOf p (Subgroup.normalizer (S : Set C))).map C.subtype =
      CFSG.Open.pCoreOf p (C ⊓ Subgroup.normalizer (S.map C.subtype : Set X)) := by
  rw [← pCoreOf_map_of_injective p C.subtype C.subtype_injective,
    map_subtype_normalizer_eq C S]

theorem isRadicalPGroup_top_map_subtype_iff (p : ℕ) (S : Subgroup C) :
    IsRadicalPGroup p (⊤ : Subgroup C) S ↔ IsRadicalPGroup p C (S.map C.subtype) := by
  constructor
  · intro h
    unfold IsRadicalPGroup at h ⊢
    have h' : CFSG.Open.pCoreOf p (Subgroup.normalizer (S : Set C)) = S := by
      simpa only [top_inf_eq] using h
    have hmap : (CFSG.Open.pCoreOf p (Subgroup.normalizer (S : Set C))).map C.subtype =
        S.map C.subtype := by rw [h']
    rw [← pCoreOf_map_subtype_normalizer C p S, hmap]
  · intro h
    unfold IsRadicalPGroup at h ⊢
    have hmap : (CFSG.Open.pCoreOf p (Subgroup.normalizer (S : Set C))).map C.subtype =
        S.map C.subtype := by
      rw [pCoreOf_map_subtype_normalizer C p S]
      simpa only [top_inf_eq] using h
    have := Subgroup.map_injective C.subtype_injective hmap
    simpa only [top_inf_eq] using this

theorem mem_oppositePRadicals_map_subtype_iff (p : ℕ) (S V : Subgroup C) :
    V ∈ oppositePRadicals p (⊤ : Subgroup C) S ↔
      V.map C.subtype ∈ oppositePRadicals p C (S.map C.subtype) := by
  unfold oppositePRadicals
  simp only [Set.mem_setOf_eq]
  rw [isRadicalPGroup_top_map_subtype_iff C p V]
  constructor
  · rintro ⟨hrad, hcard, hinf⟩
    refine ⟨hrad, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective C.subtype_injective,
        Subgroup.card_map_of_injective C.subtype_injective, hcard]
    · have hinf' : V ⊓ Subgroup.normalizer (S : Set C) = ⊥ := by simpa using hinf
      rw [← map_subtype_normalizer_eq C S,
        ← Subgroup.map_inf_eq V (Subgroup.normalizer (S : Set C)) C.subtype
          C.subtype_injective, hinf', Subgroup.map_bot]
  · rintro ⟨hrad, hcard, hinf⟩
    refine ⟨hrad, ?_, ?_⟩
    · rw [← Subgroup.card_map_of_injective (f := C.subtype) (K := V) C.subtype_injective,
        ← Subgroup.card_map_of_injective (f := C.subtype) (K := S) C.subtype_injective, hcard]
    · have hinf' : V.map C.subtype ⊓ (C ⊓ Subgroup.normalizer (S.map C.subtype : Set X)) =
          ⊥ := hinf
      rw [← map_subtype_normalizer_eq C S,
        ← Subgroup.map_inf_eq V (Subgroup.normalizer (S : Set C)) C.subtype
          C.subtype_injective,
        Subgroup.map_eq_bot_iff_of_injective (H := V ⊓ Subgroup.normalizer (S : Set C))
          (f := C.subtype) C.subtype_injective] at hinf'
      simpa using hinf'

theorem map_subtype_map_conj (A : Subgroup C) (u : C) :
    (A.map (MulAut.conj u).toMonoidHom).map C.subtype =
      (A.map C.subtype).map (MulAut.conj (C.subtype u)).toMonoidHom := by
  have h : C.subtype.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (C.subtype u)).toMonoidHom.comp C.subtype := by
    ext x
    simp [MulAut.conj_apply]
  rw [Subgroup.map_map, Subgroup.map_map, h]

theorem hasGoodOppositePRadicals_top_of_map_subtype {p : ℕ} {S : Subgroup C}
    (h : HasGoodOppositePRadicals p C (S.map C.subtype)) :
    HasGoodOppositePRadicals p (⊤ : Subgroup C) S := by
  obtain ⟨V₀', hV₀', hgen', hconj'⟩ := h
  have hV₀'le : V₀' ≤ C := hV₀'.1.le
  let V₀ : Subgroup C := V₀'.subgroupOf C
  have hV₀map : V₀.map C.subtype = V₀' := Subgroup.map_subgroupOf_eq_of_le hV₀'le
  have hV₀ : V₀ ∈ oppositePRadicals p (⊤ : Subgroup C) S := by
    rw [mem_oppositePRadicals_map_subtype_iff C p S V₀, hV₀map]
    exact hV₀'
  have hgen : S ⊔ V₀ = ⊤ := by
    have hm : (S ⊔ V₀).map C.subtype = (⊤ : Subgroup C).map C.subtype := by
      rw [Subgroup.map_sup, hV₀map, hgen', Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective C.subtype_injective hm
  refine ⟨V₀, hV₀, hgen, fun W hW => ?_⟩
  have hW' : W.map C.subtype ∈ oppositePRadicals p C (S.map C.subtype) :=
    (mem_oppositePRadicals_map_subtype_iff C p S W).mp hW
  obtain ⟨u, hu, huW⟩ := hconj' _ hW'
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
  refine ⟨u₀, hu₀, ?_⟩
  have hmaps : W.map C.subtype = ((V₀.map (MulAut.conj u₀).toMonoidHom)).map C.subtype := by
    rw [huW, ← hV₀map, ← map_subtype_map_conj]
  exact Subgroup.map_injective C.subtype_injective hmaps

end SubtypeTransport


end CFSG.GroupTheory
