module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Defs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

section General

theorem pow_dvd_card_of_not_dvd_index {Λ : Type*} [Group Λ] [Finite Λ] {J : Subgroup Λ} {k : ℕ}
    (hidx : ¬ 3 ∣ J.index) (hΛ : 3 ^ k ∣ Nat.card Λ) : 3 ^ k ∣ Nat.card J := by
  have h := J.card_mul_index
  have hcop : Nat.Coprime (3 ^ k) J.index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx)
  rw [← h] at hΛ
  exact hcop.dvd_of_dvd_mul_right hΛ

theorem exists_card_eq_two_pow_mul {J Q : Type*} [Group J] [Finite J] [Group Q]
    (e : J ⧸ CFSG.pCore 2 J ≃* Q) : ∃ a : ℕ, Nat.card J = 2 ^ a * Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := J)).exists_card_eq
  refine ⟨a, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 J), ha,
    Nat.card_congr e.toEquiv, mul_comm]

theorem false_of_index_perm {Λ : Type*} [Group Λ] [Finite Λ] {J : Subgroup Λ} {n a : ℕ}
    (hidx : ¬ 3 ∣ J.index) (hΛ : 9 ∣ Nat.card Λ) (hn : n ≤ 4)
    (hJ : Nat.card J = 2 ^ a * n.factorial) : False := by
  have h9 := pow_dvd_card_of_not_dvd_index (k := 2) hidx (by simpa using hΛ)
  rw [hJ] at h9
  have h24 : n.factorial ∣ 24 := Nat.factorial_dvd_factorial hn
  have hcop : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
  have h9' : 9 ∣ n.factorial := hcop.dvd_of_dvd_mul_left (by simpa using h9)
  have := h9'.trans h24
  omega

theorem nine_dvd_card_alternatingGroup {m : ℕ} (hm : 6 ≤ m) :
    9 ∣ Nat.card (alternatingGroup (Fin m)) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp only [Fintype.card_fin]
  have h720 : (720 : ℕ) ∣ m.factorial := by
    have := Nat.factorial_dvd_factorial hm
    simpa [Nat.factorial] using this
  exact Nat.dvd_div_of_mul_dvd (by omega)

theorem le_four_of_isSolvable_perm {n : ℕ} (h : Group.IsSolvable (Equiv.Perm (Fin n))) :
    n ≤ 4 := by
  by_contra hn
  exact Equiv.Perm.not_isSolvable (Fin n) (by simpa using (by omega : 5 ≤ n)) h

end General

section BarM

variable {G : Type} [Group G]

theorem not_dvd_index_barM {M L Y : Subgroup G} (hLM : L ≤ M)
    (h : ¬ 3 ∣ (Y.subgroupOf L).index) :
    ¬ 3 ∣ ((barM M Y).subgroupOf (barM M L)).index := by
  let f : ↥L →* ↥(barM M L) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hLM)).codRestrict (barM M L)
      (fun x => ⟨⟨x, hLM x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, Subtype.ext rfl⟩
  have hle : Y.subgroupOf L ≤ ((barM M Y).subgroupOf (barM M L)).comap f := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨⟨x, hLM x.2⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), rfl⟩
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_comap_of_surjective _ hf] at hdvd
  exact fun h3 => h (h3.trans hdvd)

theorem isSolvable_barM {M Y : Subgroup G} (hYM : Y ≤ M) (h : Group.IsSolvable ↥Y) :
    Group.IsSolvable ↥(barM M Y) := by
  let g : ↥Y →* ↥(barM M Y) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hYM)).codRestrict (barM M Y)
      (fun x => ⟨⟨x, hYM x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, Subtype.ext rfl⟩
  have := h
  exact Group.isSolvable_of_surjective hg

theorem not_isSolvable_barM_center_quotient {M L : Subgroup G} (hL : IsTwoPrimeComponent M L) :
    ¬ Group.IsSolvable (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
  have hLb : IsComponentOf (barM M L) ⊤ := hL.component
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
    hLb.2.2
  have : IsSimpleGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hLb.2.2.2
  intro hs
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)

theorem not_isSolvable_barM {M L : Subgroup G} (hL : IsTwoPrimeComponent M L) :
    ¬ Group.IsSolvable ↥(barM M L) := by
  intro h
  have := h
  exact not_isSolvable_barM_center_quotient hL (Group.isSolvable_of_surjective
    (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))))

theorem card_subgroupOf_barM {M L Y : Subgroup G} (hYL : Y ≤ L) :
    Nat.card ↥((barM M Y).subgroupOf (barM M L)) = Nat.card ↥(barM M Y) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (barM_mono hYL)).toEquiv

end BarM

section Shapes

variable {G : Type} [Group G] [Finite G]

theorem card_dvd_seventy_two {K : Type*} [Group K] [Finite K] (Z : Subgroup K) [Z.Normal]
    (hZ : Nat.card Z = 3) (P : Subgroup K)
    (hP : Nonempty (↥(P.map (QuotientGroup.mk' Z)) ≃* Equiv.Perm (Fin 4))) :
    Nat.card P ∣ 72 := by
  obtain ⟨e⟩ := hP
  set q : K →* K ⧸ Z := QuotientGroup.mk' Z with hq
  let f : P →* K ⧸ Z := q.comp P.subtype
  have hrange : f.range = P.map q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hr : Nat.card f.range = 24 := by
    rw [hrange, Nat.card_congr e.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have hk : Nat.card f.ker ∣ 3 := by
    rw [← hZ]
    refine Subgroup.card_dvd_of_injective
      ((P.subtype.comp f.ker.subtype).codRestrict Z fun x => ?_) ?_
    · have h := x.2
      rw [MonoidHom.mem_ker] at h
      exact (QuotientGroup.eq_one_iff _).mp h
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : ↥Z → K) hxy))
  rw [← Subgroup.card_ker_mul_card_range f, hr]
  have := Nat.mul_dvd_mul hk (dvd_refl 24)
  simpa using this

theorem false_of_nineThreeFour {M S L : Subgroup G}
    (hJidx : ¬ 3 ∣ ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).index)
    (h4 : NineThreeFour M S L) : False := by
  obtain ⟨-, hZ, ⟨e⟩, -, hP⟩ := h4
  have hLb : Nat.card ↥(barM M L) = 1080 := by
    have : Nontrivial (Fin 6) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(barM M L)), hZ,
      Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have h72 := card_dvd_seventy_two (Subgroup.center ↥(barM M L)) hZ _ hP
  have h27 := pow_dvd_card_of_not_dvd_index (k := 3) hJidx (by rw [hLb]; norm_num)
  have := h27.trans h72
  omega

theorem false_of_nineThreeSix {M S L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hJsolv : Group.IsSolvable ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    (hJidx : ¬ 3 ∣ ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).index)
    (h6 : NineThreeSix M S L) : False := by
  obtain ⟨-, n, ⟨e1⟩, ⟨e2⟩⟩ := h6
  have hperm : Group.IsSolvable (Equiv.Perm (Fin n)) :=
    Group.isSolvable_of_surjective (f := e2.toMonoidHom) e2.surjective
  have hn4 := le_four_of_isSolvable_perm hperm
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hA : Group.IsSolvable (alternatingGroup (Fin (2 * n))) :=
      alternatingGroup.isSolvable (by simp; omega)
    exact not_isSolvable_barM_center_quotient hL
      (Group.isSolvable_of_surjective (f := e1.symm.toMonoidHom) e1.symm.surjective)
  have h9 : 9 ∣ Nat.card ↥(barM M L) := by
    have h := nine_dvd_card_alternatingGroup (m := 2 * n) (by omega)
    rw [← Nat.card_congr e1.toEquiv] at h
    exact h.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨a, ha⟩ := exists_card_eq_two_pow_mul e2
  refine false_of_index_perm hJidx h9 hn4 (a := a) ?_
  rw [card_subgroupOf_barM inf_le_right, ha, Nat.card_perm]
  simp

theorem false_of_nineThreeSeven {M S L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hJsolv : Group.IsSolvable ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    (hJidx : ¬ 3 ∣ ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).index)
    (h7 : NineThreeSeven M S L) : False := by
  obtain ⟨-, n, ⟨e1⟩, ⟨e2⟩⟩ := h7
  have hperm : Group.IsSolvable (Equiv.Perm (Fin n)) :=
    Group.isSolvable_of_surjective (f := e2.toMonoidHom) e2.surjective
  have hn4 := le_four_of_isSolvable_perm hperm
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hA : Group.IsSolvable (alternatingGroup (Fin (4 * n))) :=
      alternatingGroup.isSolvable (by simp; omega)
    exact not_isSolvable_barM hL
      (Group.isSolvable_of_surjective (f := e1.symm.toMonoidHom) e1.symm.surjective)
  have h9 : 9 ∣ Nat.card ↥(barM M L) := by
    have h := nine_dvd_card_alternatingGroup (m := 4 * n) (by omega)
    rwa [← Nat.card_congr e1.toEquiv] at h
  obtain ⟨a, ha⟩ := exists_card_eq_two_pow_mul e2
  refine false_of_index_perm hJidx h9 hn4 (a := a) ?_
  rw [card_subgroupOf_barM inf_le_right, ha, Nat.card_perm]
  simp

omit [Finite G] in
theorem false_of_nineThreeEight {M S L : Subgroup G}
    (hJsolv : Group.IsSolvable ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    (h8 : NineThreeEight M S L) : False := by
  obtain ⟨-, N, r, hN, h2r, h0, h2, h4, -, φ, -⟩ := h8
  have hprod : Group.IsSolvable (Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))) :=
    Group.isSolvable_of_surjective (f := φ.toMonoidHom) φ.surjective
  have hs : Group.IsSolvable (Equiv.Perm (Fin (N - 2 * r))) :=
    Group.isSolvable_of_surjective (f := MonoidHom.snd (Equiv.Perm (Fin r))
      (Equiv.Perm (Fin (N - 2 * r)))) fun b => ⟨(1, b), rfl⟩
  have hle := le_four_of_isSolvable_perm hs
  obtain ⟨k, hk⟩ := hN
  omega

end Shapes

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_mulAut_of_blockHyps (hK : KFactBlockSylowThreeAut) {M S L : Subgroup G}
    (hyps : BlockL28Hyps M S L) (hQS : pCoreOf 2 M ≤ S)
    (hsolv : Group.IsSolvable ↥(Subgroup.normalizer (S : Set G) ⊓ L))
    (hidx : ¬ 3 ∣ ((Subgroup.normalizer (S : Set G) ⊓ L).subgroupOf L).index) :
    ¬ 27 ∣ Nat.card (MulAut ↥(barM M L)) := by
  have hL : IsTwoPrimeComponent M L := hyps.2.2.1.toIsTwoPrimeComponent
  have hLM : L ≤ M := hL.le
  have hJsolv : Group.IsSolvable ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) :=
    isSolvable_barM (inf_le_right.trans hLM) hsolv
  have hJidx := not_dvd_index_barM hLM hidx
  rcases hyps.2.2.2.1 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hyps.2.2.2.2.1
  · exact hK G M S L hyps hQS (Or.inl h2) hsolv hidx
  · exact hK G M S L hyps hQS (Or.inr (Or.inl h3)) hsolv hidx
  · exact (false_of_nineThreeFour hJidx h4).elim
  · exact hK G M S L hyps hQS (Or.inr (Or.inr h5)) hsolv hidx
  · exact (false_of_nineThreeSix hL hJsolv hJidx h6).elim
  · exact (false_of_nineThreeSeven hL hJsolv hJidx h7).elim
  · exact (false_of_nineThreeEight hJsolv h8).elim

end CFSG.LocalAnalysis.RankThreeTheoremC
