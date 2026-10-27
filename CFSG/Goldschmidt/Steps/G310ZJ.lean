module

public import CFSG.Goldschmidt.Steps.G310ZJBasic
public import CFSG.Goldschmidt.Steps.G310Odd
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.Walter.Bender1970.S1.ZJ
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem3_2
import CFSG.Walter.Bender1970.S1.QdNotInvolved
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open CFSG.Glauberman
open scoped commutatorElement

section Stab

variable {X : Type*} [Group X] [Finite X]

theorem pStable_of_hasAbelianSylowTwo
    (hG : CFSG.Walter.HasAbelianSylowTwo X) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) : pStable p X := by
  have hstab : pStable p ((⊤ : Subgroup X) ⧸ (⊥ : Subgroup (⊤ : Subgroup X))) :=
    (lemma6_3 hp2).mp (CFSG.Walter.qd_not_involved_of_hasAbelianSylowTwo hG hp2) ⊤ ⊥
  exact (pStable_iso (QuotientGroup.quotientBot.trans Subgroup.topEquiv)).mp hstab

theorem hasAbelianSylowTwo_of_odd {Y : Type*} [Group Y] [Finite Y] (hY : Odd (Nat.card Y)) :
    CFSG.Walter.HasAbelianSylowTwo Y := by
  intro S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : (S : Subgroup Y) = ⊥ := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    have hdvd : 2 ^ n ∣ Nat.card Y := hn ▸ Subgroup.card_subgroup_dvd_card _
    rcases n with _ | n
    · rw [pow_zero] at hn
      exact Subgroup.card_eq_one.mp hn
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd)
        (fun h => (Nat.not_even_iff_odd.mpr hY) (even_iff_two_dvd.mpr h))
  rw [hS]
  infer_instance

end Stab

section ZJOdd

variable {X : Type*} [Group X] [Finite X]

theorem normalizer_le_normalizer_zj_of_odd
    {p : ℕ} [Fact p.Prime] {Y P F : Subgroup X}
    (hYodd : Odd (Nat.card Y)) (hsyl : fusionIsSylowIn p P Y) (hFY : F ≤ Y)
    (hYF : Y ≤ Subgroup.normalizer (F : Set X)) (hFp : IsPGroup p F)
    (hC : Y ⊓ Subgroup.centralizer (F : Set X) ≤ F) :
    Subgroup.normalizer (Y : Set X) ≤ Subgroup.normalizer (ZJ P : Set X) := by
  have hA := hasAbelianSylowTwo_of_odd hYodd
  obtain ⟨S, hS⟩ := exists_sylow_of_fusionIsSylowIn hsyl
  have hSP : (S : Subgroup Y) = P.subgroupOf Y := by
    rw [← hS]
    exact (Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _).symm
  have hFn : (F.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hFY).mpr hYF
  have hFle : F.subgroupOf Y ≤ CFSG.pCore p Y := le_sSup ⟨hFn, hFp.comap_subtype⟩
  have hCY : Subgroup.centralizer ((CFSG.pCore p Y : Subgroup Y) : Set Y) ≤ CFSG.pCore p Y := by
    refine (Subgroup.centralizer_le hFle).trans (le_trans ?_ hFle)
    intro y hy
    refine hC ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy ⟨f, hFY hf⟩ hf)
  have hchar := CFSG.Walter.bender1970_1_2_ZJ_characteristic hA S hCY
  rw [hSP] at hchar
  have hZ : ZJ P = (ZJ (P.subgroupOf Y)).map Y.subtype := by
    have := zj_map Y.subtype Y.subtype_injective (P.subgroupOf Y)
    rwa [Subgroup.map_subgroupOf_eq_of_le hsyl.1] at this
  intro g hg
  apply mem_normalizer_of_map_le
  rw [hZ]
  rintro _ ⟨x, hx, rfl⟩
  exact CFSG.Walter.conj_mem_map_of_characteristic hg hx

omit [Finite X] in
theorem fusionIsSylowIn_sup_of_inf {p : ℕ} {P O : Subgroup X} (hPp : IsPGroup p P)
    (hPO : P ≤ Subgroup.normalizer (O : Set X)) (hc : fusionIsSylowIn p (P ⊓ O) O) :
    fusionIsSylowIn p P (P ⊔ O) := by
  refine ⟨le_sup_left, hPp, fun Q hQ hQp hPQ => le_antisymm (fun s hs => ?_) hPQ⟩
  obtain ⟨q, hq, o, ho, rfl⟩ := exists_mul_of_mem_sup hPO (hQ hs)
  have hoQ : o ∈ Q := by
    have := Q.mul_mem (Q.inv_mem (hPQ hq)) hs
    simpa using this
  have h1 : Q ⊓ O = P ⊓ O :=
    hc.2.2 _ inf_le_right (hQp.to_le inf_le_left) (inf_le_inf_right _ hPQ)
  have hoP : o ∈ P ⊓ O := by
    rw [← h1]
    exact ⟨hoQ, ho⟩
  exact P.mul_mem hq hoP.1

end ZJOdd

section Main

variable {X : Type*} [Group X] [Finite X]

theorem zj_normal_of_core
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h2 : CFSG.Walter.HasAbelianSylowTwo X) {P : Subgroup X} (hPp : IsPGroup p P)
    (hb : ∀ B : Subgroup X, B.Normal → IsPGroup p B → B ≤ P)
    (hc : fusionIsSylowIn p (P ⊓ goldschmidtOddCore X) (goldschmidtOddCore X))
    (hd : Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (he : ∀ N N' : Subgroup X, N.Normal → N'.Normal → N' ≤ N →
      (∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k ∈ N') →
      N ≤ goldschmidtOddCore X ∨ (⊤ : Subgroup X) ≤ N' ⊔ goldschmidtOddCore X ⊔ P) :
    (ZJ P).Normal := by
  classical
  have hp : p.Prime := Fact.out
  set O := goldschmidtOddCore X with hOdef
  set Z := ZJ P with hZdef
  set F := CFSG.pCore p X with hFdef
  have hOodd : Odd (Nat.card O) := SStarTransport.odd_card_goldschmidtOddCore X
  have hOnot : ¬ 2 ∣ Nat.card O := fun h =>
    (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  have hFn : F.Normal := CFSG.pCore_normal
  have hFp : IsPGroup p F := CFSG.pCore_isPGroup
  have hFP : F ≤ P := hb F hFn hFp
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨n, hn⟩ := hFp.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hFO : F ≤ O := le_sSup ⟨hFn, hFodd⟩
  have hZP : Z ≤ P := zj_le P
  have hZab : IsMulCommutative Z := isMulCommutative_zj P
  have hPZ : P ≤ Subgroup.normalizer (Z : Set X) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_zj P)
  have hPO : P ≤ Subgroup.normalizer (O : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (goldschmidtOddCore_normal X)]
    exact le_top
  have hFtop : (⊤ : Subgroup X) ≤ Subgroup.normalizer (F : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hFn]
  have hPOsyl := fusionIsSylowIn_sup_of_inf hPp hPO hc
  have hPOodd : Odd (Nat.card (P ⊔ O : Subgroup X)) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (not_two_dvd_card_sup hp hp2 hPp hPO hOnot))
  have hZPO : P ⊔ O ≤ Subgroup.normalizer (Z : Set X) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_zj_of_odd hPOodd hPOsyl
      (hFP.trans le_sup_left) (le_top.trans hFtop) hFp (inf_le_right.trans hd))
  set P₁ := P ⊓ O with hP₁
  have hZ₁ : (ZJ P₁).Normal := by
    have h1 := normalizer_le_normalizer_zj_of_odd hOodd hc hFO (le_top.trans hFtop) hFp
      (inf_le_right.trans hd)
    rw [Subgroup.normalizer_eq_top_iff.mpr (goldschmidtOddCore_normal X)] at h1
    exact Subgroup.normalizer_eq_top_iff.mp (top_unique h1)
  by_cases hF1 : F = ⊥
  · have hall : ∀ x : X, x = 1 := by
      intro x
      have hx : x ∈ Subgroup.centralizer (F : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [hF1, Subgroup.coe_bot, Set.mem_singleton_iff] at hh
        rw [hh, one_mul, mul_one]
      have := hd hx
      rwa [hF1, Subgroup.mem_bot] at this
    have hZbot : Z = ⊥ := by
      rw [eq_bot_iff]
      intro z _
      rw [Subgroup.mem_bot]
      exact hall z
    rw [hZbot]
    infer_instance
  have hstab := pStable_of_hasAbelianSylowTwo h2 hp2
  have hZF : Z ≤ F := by
    intro z hz
    have h1 : ⁅⁅F, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥ :=
      commutator_zpowers_le_of_mem
        (commutator_commutator_eq_bot_of_abelian_normalizer (hFP.trans hPZ) hZab) hz
    have h2 := pStableLocal_apply_of_normal_pSubgroup p hstab hF1 hFp hFn z h1
    have h3 := pCore_quotient_centralizer_le_of_centralizer_le_core p hd h2
    obtain ⟨f, hf, hfz⟩ := h3
    have h4 : f⁻¹ * z ∈ Subgroup.centralizer (F : Set X) := by
      rw [← QuotientGroup.eq]
      exact hfz
    have := F.mul_mem hf (hd h4)
    simpa using this
  by_contra hZn
  have : Finite (Subgroup X) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨B, ⟨hBn, hBp, hBZ⟩, hBmin⟩ := exists_minimal_of_wellFoundedLT
    (fun B : Subgroup X => B.Normal ∧ IsPGroup p B ∧ ¬ (B ⊓ Z).Normal)
    ⟨F, hFn, hFp, by rwa [inf_eq_right.mpr hZF]⟩
  have hB1 : Subgroup.normalClosure ((B ⊓ Z : Subgroup X) : Set X) = B := by
    set B₁ := Subgroup.normalClosure ((B ⊓ Z : Subgroup X) : Set X) with hB₁
    have hB₁B : B₁ ≤ B := Subgroup.normalClosure_le_normal inf_le_left
    have hB₁n : B₁.Normal := Subgroup.normalClosure_normal
    have hZB₁ : (B ⊓ Z) ≤ B₁ := Subgroup.le_normalClosure
    by_contra hne
    apply hBZ
    have hB₁Z : (B₁ ⊓ Z).Normal := by
      by_contra hB₁Z
      exact hne (le_antisymm hB₁B (hBmin ⟨hB₁n, hBp.to_le hB₁B, hB₁Z⟩ hB₁B))
    have h1 : B₁ ≤ B₁ ⊓ Z := Subgroup.normalClosure_le_normal (le_inf hZB₁ inf_le_right)
    have h2 : (B ⊓ Z) = B₁ := le_antisymm hZB₁ (le_inf hB₁B (h1.trans inf_le_right))
    rw [h2]
    exact hB₁n
  have hBle : ∀ K : Subgroup X, K.Normal → B ⊓ Z ≤ K → B ≤ K := fun K _ h =>
    calc B = Subgroup.normalClosure ((B ⊓ Z : Subgroup X) : Set X) := hB1.symm
      _ ≤ K := Subgroup.normalClosure_le_normal h
  have hBP : B ≤ P := hb B hBn hBp
  have hBne : B ≠ ⊥ := by
    rintro rfl
    apply hBZ
    rw [bot_inf_eq]
    infer_instance
  have hB'Z : ⁅B, B⁆ ≤ Z := by
    have : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hBne
    have : Group.IsNilpotent B := hBp.isNilpotent
    have : Group.IsSolvable B := IsNilpotent.to_isSolvable
    have hlt : ⁅B, B⁆ < B := CFSG.commutator_lt_self_of_isSolvable B
    have hB'n : (⁅B, B⁆ : Subgroup X).Normal := inferInstance
    have hN : (⁅B, B⁆ ⊓ Z).Normal := by
      by_contra hN
      exact (not_le_of_gt hlt) (hBmin ⟨hB'n, hBp.to_le hlt.le, hN⟩ hlt.le)
    set N := ⁅B, B⁆ ⊓ Z with hNdef
    have hCN : (B ⊓ Z) ≤ (Subgroup.centralizer ((B.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) :
        Set (X ⧸ N))).comap (QuotientGroup.mk' N) := by
      intro z hz
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hbz : ⁅b, z⁆ ∈ N := by
        refine ⟨Subgroup.commutator_mem_commutator hb hz.1, ?_⟩
        have h1 : b * z * b⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hPZ (hBP hb)) z).mp hz.2
        rw [commutatorElement_def]
        exact Z.mul_mem h1 (Z.inv_mem hz.2)
      have h2 := (QuotientGroup.eq_one_iff (N := N) _).mpr hbz
      rw [commutatorElement_def] at h2
      simp only [QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h2
      calc (b : X ⧸ N) * (z : X ⧸ N) = ((b : X ⧸ N) * z * (b : X ⧸ N)⁻¹ * (z : X ⧸ N)⁻¹) *
          (z : X ⧸ N) * (b : X ⧸ N) := by group
        _ = (z : X ⧸ N) * (b : X ⧸ N) := by rw [h2, one_mul]
    have hCNn : ((Subgroup.centralizer ((B.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) :
        Set (X ⧸ N))).comap (QuotientGroup.mk' N)).Normal := by
      have : (B.map (QuotientGroup.mk' N)).Normal :=
        hBn.map _ (QuotientGroup.mk'_surjective N)
      have : (Subgroup.centralizer ((B.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) :
          Set (X ⧸ N))).Normal := Subgroup.normal_centralizer
      exact Subgroup.Normal.comap inferInstance _
    have hBC : B ≤ (Subgroup.centralizer ((B.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) :
        Set (X ⧸ N))).comap (QuotientGroup.mk' N) := hBle _ hCNn hCN
    have hcomm : ⁅B, B⁆.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨b, hb, rfl⟩
      exact hBC hb
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hcomm
    exact hcomm.trans inf_le_right
  have hB'C : ⁅B, B⁆ ≤ Subgroup.centralizer (B : Set X) := by
    have hB'n : (⁅B, B⁆ : Subgroup X).Normal := inferInstance
    have : (Subgroup.centralizer ((⁅B, B⁆ : Subgroup X) : Set X)).Normal :=
      Subgroup.normal_centralizer
    have hZC : (B ⊓ Z) ≤ Subgroup.centralizer ((⁅B, B⁆ : Subgroup X) : Set X) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact mul_comm_of_isMulCommutative hZab (hB'Z hc) hz.2
    have h1 : B ≤ Subgroup.centralizer ((⁅B, B⁆ : Subgroup X) : Set X) :=
      hBle _ inferInstance hZC
    exact Subgroup.le_centralizer_iff.mp h1
  set C := Subgroup.centralizer (B : Set X) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  set Cs := (CFSG.pCore p (X ⧸ C)).comap (QuotientGroup.mk' C) with hCs
  have hCsn : Cs.Normal := Subgroup.Normal.comap CFSG.pCore_normal _
  have hCCs : C ≤ Cs := by
    intro c hc
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff c).mpr hc]
    exact Subgroup.one_mem _
  have hCsp : ∀ x ∈ Cs, ∃ k : ℕ, x ^ p ^ k ∈ C := by
    intro x hx
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := X ⧸ C) ⟨_, hx⟩
    refine ⟨k, (QuotientGroup.eq_one_iff _).mp ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hCsO : Cs ≤ O := by
    rcases he Cs C hCsn hCn hCCs hCsp with h | h
    · exact h
    · exfalso
      apply hBZ
      have hZN : (⊤ : Subgroup X) ≤ Subgroup.normalizer ((B ⊓ Z : Subgroup X) : Set X) := by
        refine h.trans (sup_le (sup_le ?_ ?_) ?_)
        · intro c hc
          apply Subgroup.centralizer_le_normalizer
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          exact Subgroup.mem_centralizer_iff.mp hc z hz.1
        · exact le_normalizer_inf (fun o _ => by
            rw [Subgroup.normalizer_eq_top_iff.mpr hBn]
            exact Subgroup.mem_top o) (le_sup_right.trans hZPO)
        · exact le_normalizer_inf (fun q _ => by
            rw [Subgroup.normalizer_eq_top_iff.mpr hBn]
            exact Subgroup.mem_top q) hPZ
      exact Subgroup.normalizer_eq_top_iff.mp (top_unique hZN)
  have hPB : P ≤ Subgroup.normalizer (B : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hBn]
    exact le_top
  rcases forall_le_or_exists_le_normalizer' hp (hp.odd_of_ne_two hp2) hPp hBP hPB hB'C hB'Z with
    h | ⟨A, hA, hBA, hBN⟩
  · apply hBZ
    have hBZ' : B ≤ Z := fun b hb => mem_zj_iff.mpr fun A hA => h A hA hb
    rw [inf_eq_left.mpr hBZ']
    exact hBn
  ·
    have hBAA : ⁅⁅B, A⁆, A⁆ = ⊥ := by
      have h1 : ⁅B, A⁆ ≤ A := Subgroup.le_normalizer_iff_commutator_le_right.mp hBN
      have h2 : ⁅A, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.2.1)
      exact le_bot_iff.mp (h2 ▸ Subgroup.commutator_mono h1 le_rfl)
    have hACs : A ≤ Cs := by
      intro x hx
      exact pStableLocal_apply_of_normal_pSubgroup p hstab hF1 hBp hBn x
        (commutator_zpowers_le_of_mem hBAA hx)
    have hAP₁ : A ≤ P₁ := le_inf hA.1 (hACs.trans hCsO)
    have hZZ₁ : Z ≤ ZJ P₁ := zj_le_zj inf_le_left hA hAP₁
    have hBZ₁ : B ≤ ZJ P₁ := by
      have : (B ⊓ ZJ P₁).Normal := Subgroup.normal_inf_normal _ _
      have h1 : B ≤ B ⊓ ZJ P₁ := hBle _ inferInstance (inf_le_inf_left _ hZZ₁)
      exact h1.trans inf_le_right
    exact hBA (hBZ₁.trans (zj_le_of_mem
      (CFSG.thompsonAbelianSubgroups_mem_of_le inf_le_left hA hAP₁)))

end Main

end CFSG.Goldschmidt.G310
