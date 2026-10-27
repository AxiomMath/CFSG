module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9TwE6Abs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LabHolds2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Field
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9E6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup lieOrderBridge_holds)

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

open CFSG.LocalAnalysis.GLTheoremA.I2018 (catalogIs_congr' fixSubgroup_one_eq_top)


private theorem twE6_exists_surjection {Γ : Type} [Group Γ] {K J : Subgroup Γ} (hJK : J ≤ K)
    {T : Type} [Group T] (e : PSimple 3 K ≃* T) :
    ∃ π : ↥J →* ↥((chevTransfer 3 K J).map e.toMonoidHom), Function.Surjective π ∧
      ∀ j : ↥J, ((π j : ↥((chevTransfer 3 K J).map e.toMonoidHom)) : T) =
        e (chevQuotHom 3 K (Subgroup.inclusion hJK j)) := by
  refine ⟨((e.toMonoidHom.comp (chevQuotHom 3 K)).comp (Subgroup.inclusion hJK)).codRestrict _
    (fun j => ?_), ?_, fun j => rfl⟩
  · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 j.2))
  · rintro ⟨t, ht⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hs
    exact ⟨⟨k, Subgroup.mem_subgroupOf.1 hk⟩, rfl⟩

section Certs


theorem i141U9Fam_twE6Two_of (hB : TwE6U38Centre) (hC : TwE6CoverNoSU38) :
    I141U9Fam u9FamTwE6Two := by
  intro Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  have hxN : x ∈ Subgroup.normalizer (K : Set Γ) := hI1.1 (Subgroup.mem_zpowers x)
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hlabAll : Y10F.HasLabel (PQuot 3 K) (fun _ => True) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hI1.2
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) := Y10F.hasLabel_isQuasisimple hlabAll
  obtain ⟨hs, hna⟩ := u9_simple_nonabelian hI1
  obtain ⟨-, -, ⟨eJ⟩⟩ := u9_transfer_chev hx hI1 hJ
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | lie d' =>
    obtain ⟨d, hv⟩ := d'
    cases d with
    | twistedE6 q =>
      have hq2 : q.card = 2 := by simpa [u9FamTwE6Two, onLie] using hi
      have hi' : S9.isTE6two (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩) := by
        simpa [S9.isTE6two, onLie] using hq2
      have hqp : q.p = 2 := by
        have h1 : q.p ∣ 2 := by
          rw [← hq2, TauCeti.PrimePower.card_def]
          exact dvd_pow_self _ q.exponent_pos.ne'
        exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
      have hd2 : (⟨.twistedE6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic = 2 := by
        simpa using hqp
      have hα1 : chevAut 3 K ⟨x, hxN⟩ ≠ 1 := by
        intro hα1
        have hcard := u9_card_of_chevAut_eq_one hx hI1 hJ hJU hα1
        rw [lieOrderBridge_holds ⟨.twistedE6 q, hv⟩ _ ⟨e⟩] at hcard
        have hq2' : 2 ≤ q.card := by omega
        have := u9_orderTwistedE6_gt hq2'
        exact absurd hcard (by show orderTwistedE6 q.card ≠ 5515776; omega)
      have hβ1 : MulAut.congr e (chevAut 3 K ⟨x, hxN⟩) ≠ 1 := fun h =>
        hα1 ((MulAut.congr e).injective (by rw [map_one]; exact h))
      have hβ3 : MulAut.congr e (chevAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := by
        rw [← map_pow, chevAut_pow_eq_one 3 K hxN hx, map_one]
      haveI : Finite (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group :=
        Finite.of_equiv _ e.toEquiv
      obtain ⟨hJp', hIc⟩ := u9_gf8_component hx hxN hq hJ ⟨.twistedE6 q, hv⟩ e hd2 hβ1
      obtain ⟨π, hπ, hπval⟩ := twE6_exists_surjection hJK e
      obtain ⟨ι, -⟩ := u9_exists_pSimple_equiv_centerQuot Nat.prime_three
        (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ) hIc.2.2
        (isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJp')) π hπ
      have hcardI : Nat.card (↥((chevTransfer 3 K J).map e.toMonoidHom) ⧸
          Subgroup.center ↥((chevTransfer 3 K J).map e.toMonoidHom)) = 5515776 := by
        rw [← Nat.card_congr ι.toEquiv]
        exact CatSingle.card_isU3eight lieOrderBridge_holds hJU
      have hIZ : Subgroup.center ↥((chevTransfer 3 K J).map e.toMonoidHom) = ⊥ :=
        hB (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group
          ⟨.lie ⟨.twistedE6 q, hv⟩, hi', ⟨MulEquiv.refl _⟩⟩ _ hβ3 hβ1 _ hIc hcardI
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hQcat : catalogIs (PQuot 3 K ⧸ Subgroup.center (PQuot 3 K)) S9.isTE6two :=
        ⟨.lie ⟨.twistedE6 q, hv⟩, hi', ⟨e⟩⟩
      have hZ3 : IsPGroup 3 (Subgroup.center (PQuot 3 K)) :=
        CFSG.HardMathSupport.Solomon.Coordinator.isPGroup_center_of_pPrimeCore_eq_bot
          Nat.prime_three (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3)
      let lam : ↥J →* PQuot 3 K := (pQuotHom 3 K).comp (Subgroup.inclusion hJK)
      have hlam : Nat.Coprime 3 (Nat.card lam.ker) := by
        have hcopO : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) :=
          CFSG.pPrimeCore_coprime_card
        let g : ↥lam.ker →* ↥(GLAPPrimeCore 3 ↥K) :=
          ((Subgroup.inclusion hJK).comp lam.ker.subtype).codRestrict (GLAPPrimeCore 3 ↥K)
            (fun j => (QuotientGroup.eq_one_iff _).1 j.2)
        have hginj : Function.Injective g := by
          intro a b h
          apply Subtype.ext
          apply Subgroup.inclusion_injective hJK
          exact congrArg Subtype.val h
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective g hginj) hcopO
      let rho : PQuot 3 K →* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group :=
        e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (PQuot 3 K)))
      have hker : rho.ker = Subgroup.center (PQuot 3 K) := by
        rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective]
        exact QuotientGroup.ker_mk' _
      have hrl : ∀ j : ↥J, rho (lam j) =
          ((π j : ↥((chevTransfer 3 K J).map e.toMonoidHom)) :
            (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) := fun j => (hπval j).symm
      have hIq : CFSG.Open.IsQuasisimple ↥((chevTransfer 3 K J).map e.toMonoidHom) := hIc.2.2
      haveI : IsSimpleGroup (↥((chevTransfer 3 K J).map e.toMonoidHom) ⧸
          Subgroup.center ↥((chevTransfer 3 K J).map e.toMonoidHom)) := hIq.2
      have hIs : IsSimpleGroup ↥((chevTransfer 3 K J).map e.toMonoidHom) :=
        (((QuotientGroup.quotientMulEquivOfEq hIZ).trans QuotientGroup.quotientBot).symm).isSimpleGroup
      have hI3 : 3 ∣ Nat.card ↥((chevTransfer 3 K J).map e.toMonoidHom) := by
        refine (show 3 ∣ 5515776 by norm_num).trans ?_
        rw [← hcardI]
        exact Subgroup.card_quotient_dvd_card _
      exact (twE6_contra hC lam rho hker hq hZ3 hQcat hlam
        (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ) hZ hJU _ hIs hI3 hIZ
        (fun j => by rw [hrl j]; exact (π j).2)
        (fun t ht => by
          obtain ⟨j, hj⟩ := hπ ⟨t, ht⟩
          exact ⟨j, by rw [hrl j, hj]⟩)).elim
    | _ => exact hi.elim
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
