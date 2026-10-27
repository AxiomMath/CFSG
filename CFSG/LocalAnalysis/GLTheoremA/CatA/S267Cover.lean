module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Quot
public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop65Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.P65

variable {A : Type} [Group A] [Finite A]

theorem exists_twoGroup_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup A) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {T' : Subgroup (A ⧸ N)} (hT2 : IsPGroup 2 T') {E : Subgroup A}
    (hE : IsPGroup p E)
    (hEN : E.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer (T' : Set (A ⧸ N))) :
    ∃ T : Subgroup A, IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set A) ∧
      T.map (QuotientGroup.mk' N) = T' ∧ fusionIsSylowIn 2 T (T'.comap (QuotientGroup.mk' N)) ∧
      ∃ n : ℕ, ¬ 2 ∣ n ∧ Nat.card (T'.comap (QuotientGroup.mk' N) : Subgroup A) ∣ Nat.card T * n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : A →* A ⧸ N := QuotientGroup.mk' N with hπ
  set Y : Subgroup A := T'.comap π with hY
  have hEY : E ≤ Subgroup.normalizer (Y : Set A) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : π e ∈ Subgroup.normalizer (T' : Set (A ⧸ N)) := hEN ⟨e, he, rfl⟩
    have h2 := Subgroup.mem_normalizer_iff.1 h1 (π y)
    simp only [hY, Subgroup.mem_comap, map_mul, map_inv]
    exact h2
  have hYp : ¬ p ∣ Nat.card Y := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have hcard : Nat.card Y = Nat.card N * Nat.card T' :=
      QuotientGroup.card_preimage_mk N (T' : Set (A ⧸ N))
    rw [hcard, hk]
    intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · exact hN h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨P, hP⟩ := exists_sylow_normalized (r := 2) hEY hE hYp
  refine ⟨(P : Subgroup Y).map Y.subtype, ?_, hP, ?_, ?_, ?_⟩
  · exact (P.isPGroup').map _
  · set π' : ↥Y →* ↥T' := ((π.comp Y.subtype).codRestrict T' fun x => x.2) with hπ'
    have hπs : Function.Surjective π' := by
      intro t
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (t : A ⧸ N)
      have hat : π a = (t : A ⧸ N) := ha
      exact ⟨⟨a, show π a ∈ T' by rw [hat]; exact t.2⟩, Subtype.ext hat⟩
    have htop : ((P.mapSurjective hπs : Sylow 2 ↥T') : Subgroup ↥T') = ⊤ :=
      ((P.mapSurjective hπs).is_maximal' (hT2.of_equiv Subgroup.topEquiv.symm) le_top).symm
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact y.2
    · intro hz
      have hmem : (⟨z, hz⟩ : ↥T') ∈ ((P.mapSurjective hπs : Sylow 2 ↥T') : Subgroup ↥T') := by
        rw [htop]; exact Subgroup.mem_top _
      rw [Sylow.coe_mapSurjective] at hmem
      obtain ⟨y, hy, hyz⟩ := hmem
      exact ⟨y, ⟨y, hy, rfl⟩, congrArg Subtype.val hyz⟩
  · refine ⟨Subgroup.map_subtype_le _, (P.isPGroup').map _, fun Z hZY hZ2 hTZ => ?_⟩
    have hZ' : IsPGroup 2 (Z.subgroupOf Y) := hZ2.of_equiv (Subgroup.subgroupOfEquivOfLe hZY).symm
    have hPZ : (P : Subgroup Y) ≤ Z.subgroupOf Y := by
      intro x hx
      exact hTZ ⟨x, hx, rfl⟩
    have heq : Z.subgroupOf Y = (P : Subgroup Y) := P.is_maximal' hZ' hPZ
    calc Z = (Z.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hZY).symm
      _ = (P : Subgroup Y).map Y.subtype := by rw [heq]
  · refine ⟨(P : Subgroup Y).index, P.not_dvd_index, ?_⟩
    rw [Subgroup.card_map_of_injective Y.subtype_injective, Subgroup.card_mul_index]

theorem le_normalizer_inf' {P Q C : Subgroup A} (hQ : P ≤ Subgroup.normalizer (Q : Set A))
    (hC : P ≤ Subgroup.normalizer (C : Set A)) : P ≤ Subgroup.normalizer ((Q ⊓ C : Subgroup A) : Set A) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_inf]
  rw [Subgroup.mem_normalizer_iff.mp (hQ ha) x, Subgroup.mem_normalizer_iff.mp (hC ha) x]

theorem covers_of_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup A) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {T' : Subgroup (A ⧸ N)} (hT2 : IsPGroup 2 T')
    {M D J : Subgroup A} (hNM : N ≤ M) (hD : IsPGroup p D)
    (hJ : GLAPComponent p (M ⊓ Subgroup.centralizer (D : Set A)) J)
    (hDT : D.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer (T' : Set (A ⧸ N)))
    (hJT : J.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer (T' : Set (A ⧸ N))) :
    ∃ T : Subgroup A, IsPGroup 2 T ∧ T.map (QuotientGroup.mk' N) = T' ∧
      D ≤ Subgroup.normalizer (T : Set A) ∧ CoversMod p (Subgroup.normalizer (T : Set A)) J := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set π : A →* A ⧸ N := QuotientGroup.mk' N with hπ
  obtain ⟨T, hT2', hDT', hTmap, hTsyl, n, hn, hTn⟩ := exists_twoGroup_lift hp hp2 N hN hT2 hD hDT
  refine ⟨T, hT2', hTmap, hDT', ?_⟩
  set Y : Subgroup A := T'.comap π with hY
  set X : Subgroup A := M ⊓ Subgroup.centralizer (D : Set A) with hX
  have hJX : J ≤ X := hJ.1
  have hJC : ∀ j ∈ J, ∀ d ∈ D, d * j = j * d := fun j hj d hd =>
    Subgroup.mem_centralizer_iff.1 (hJX hj).2 d hd
  have hJY : J ≤ Subgroup.normalizer (Y : Set A) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : π j ∈ Subgroup.normalizer (T' : Set (A ⧸ N)) := hJT ⟨j, hj, rfl⟩
    have h2 := Subgroup.mem_normalizer_iff.1 h1 (π y)
    simp only [hY, Subgroup.mem_comap, map_mul, map_inv]
    exact h2
  have hTY : T ≤ Y := fun x hx => by
    show π x ∈ T'
    rw [← hTmap]; exact ⟨x, hx, rfl⟩
  have hYTN : ∀ y ∈ Y, ∃ τ ∈ T, ∃ ν ∈ N, y = τ * ν := by
    intro y hy
    have hy' : π y ∈ T.map π := by rw [hTmap]; exact hy
    obtain ⟨τ, hτ, hτy⟩ := hy'
    refine ⟨τ, hτ, τ⁻¹ * y, ?_, by group⟩
    exact (QuotientGroup.eq.1 hτy)
  have hconj : ∀ t ∈ J, ∃ ν ∈ N, GLBConj t T = GLBConj ν T := by
    intro t ht
    have hQY : GLBConj t T ≤ Y := by
      intro x hx
      have h1 : t * x * t⁻¹ ∈ T := mem_gLBConj.1 hx
      have h2 : t * x * t⁻¹ ∈ Y := hTY h1
      have := (Subgroup.mem_normalizer_iff.1 (hJY (J.inv_mem ht)) (t * x * t⁻¹)).1 h2
      simpa [mul_assoc] using this
    have hQ2 : IsPGroup 2 (GLBConj t T) := hT2'.map _
    have hcard : Nat.card (GLBConj t T : Subgroup A) = Nat.card T :=
      Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective
    have hQs : fusionIsSylowIn 2 (GLBConj t T) Y :=
      fusionIsSylowIn_of_card_dvd Nat.prime_two hQY hQ2 (by rw [hcard]; exact hTn) hn
    obtain ⟨y, hy, hyQ⟩ := exists_mem_conj_of_fusionIsSylowIn Nat.prime_two hTsyl hQs
    obtain ⟨τ, hτ, ν, hν, hyτν⟩ := hYTN y⁻¹ (Y.inv_mem hy)
    refine ⟨ν, hν, ?_⟩
    rw [hyQ, hyτν, ← gLBConj_gLBConj, gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hτ)]
  set R : Subgroup A := (Subgroup.normalizer (T : Set A) ⊓ J) ⊔ GLAPPrimeCoreOf p J with hR
  set C : Subgroup A := N ⊓ Subgroup.centralizer (D : Set A) with hC
  have hCp : ¬ p ∣ Nat.card C := fun h => hN (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hDN : D ≤ Subgroup.normalizer (N : Set A) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact le_top
  have hP : ∀ P : Subgroup A, P ≤ J → IsPGroup p P → P ≤ R := by
    intro P hPJ hP
    have hPC : P ≤ Subgroup.normalizer (C : Set A) :=
      le_normalizer_inf'
        (by rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact le_top)
        (fun g hg => Subgroup.le_normalizer (hJX (hPJ hg)).2)
    have hstab : ∀ t ∈ P, ∃ c ∈ C, GLBConj t T = GLBConj c T := by
      intro t ht
      obtain ⟨ν, hν, hνt⟩ := hconj t (hPJ ht)
      have hDt : D ≤ Subgroup.normalizer (GLBConj ν T : Set A) := by
        rw [← hνt]
        intro d hd
        rw [mem_normalizer_iff_gLBConj_eq, gLBConj_gLBConj, ← hJC t (hPJ ht) d hd,
          ← gLBConj_gLBConj, gLBConj_eq_of_mem_normalizer (hDT' hd)]
      obtain ⟨c, hc, hco⟩ := exists_conj_mem_centralizer hp hD hN hDN hDT' hν hDt
      exact ⟨c, hc, hνt.trans hco⟩
    obtain ⟨c, hc, hfix⟩ := exists_fixed_conj hp hP hCp hPC hstab
    intro t ht
    have htJ := hPJ ht
    have hcN : c * t * c⁻¹ ∈ Subgroup.normalizer (T : Set A) := by
      rw [mem_normalizer_iff_gLBConj_eq]
      have h1 := hfix t ht
      rw [gLBConj_gLBConj] at h1
      have h2 := congrArg (GLBConj c⁻¹) h1
      rwa [gLBConj_gLBConj, gLBConj_inv_gLBConj] at h2
    have hcX : c ∈ X := ⟨hNM hc.1, hc.2⟩
    have hcO : c ∈ GLAPPrimeCoreOf p X := by
      have := inf_ker_le_glaPPrimeCoreOf hp π (by rw [hπ, QuotientGroup.ker_mk']; exact hN) X
      exact this ⟨hcX, (QuotientGroup.ker_mk' N).symm ▸ hc.1⟩
    obtain ⟨hcJ, hcom⟩ := conj_mem_and_comm_mem_core hp hJ hcO htJ
    have e : t = (c * t * c⁻¹ * t⁻¹)⁻¹ * (c * t * c⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hcom))
      (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hcN, hcJ⟩))
  have hJR : J ≤ R := le_cover_of_forall_pSubgroup_le hp hp2 hJ le_sup_right hP
  unfold CoversMod
  exact le_antisymm (sup_le inf_le_right (Subgroup.map_subtype_le _)) hJR

end CFSG.LocalAnalysis.GLTheoremA.S267

end
