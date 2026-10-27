module

public import CFSG.GH74.Generic.BProg.B3.S3BootDefs
public import CFSG.GH74.Generic.BProg.B3.S3Boot152
public import CFSG.GH74.Generic.BProg.B3.S1Lemma282Bal
public import CFSG.GH74.Generic.BProg.B3.LocBalL3
public import CFSG.GH74.Generic.BProg.B2.T1Comp
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Bg.Iii2.L41Comp
public import CFSG.GH74.GLS.C3.Layer1.Th2Pump
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicExc
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicQuot
public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Comp
public import CFSG.GH74.KGroups.L3EpsUniGraph
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import Certificates.Certificate10091Base

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

namespace S3T2

variable {G : Type} [Group G] [Finite G]

theorem qShape3_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShape3 A) :
    QShape3 B := by
  obtain ⟨p, f, hp, hp2, hq, h⟩ := h
  refine ⟨p, f, hp, hp2, hq, ?_⟩
  rcases h with h | h
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
  · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)

@[expose] noncomputable def toBar {M K : Subgroup G} (hKM : K ≤ M) : ↥K →* ↥(barIn M K) :=
  ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hKM)).codRestrict
    (barIn M K) fun k => ⟨Subgroup.inclusion hKM k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩

omit [Finite G] in
theorem toBar_surjective {M K : Subgroup G} (hKM : K ≤ M) :
    Function.Surjective (toBar hKM) := by
  rintro ⟨_, ⟨m, hm, rfl⟩⟩
  exact ⟨⟨(m : G), Subgroup.mem_subgroupOf.1 hm⟩, Subtype.ext rfl⟩

theorem exists_equiv_center_quot {M K : Subgroup G} (hKM : K ≤ M)
    (hq : IsQuasisimple ↥(barIn M K))
    (hZ : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * z = z * g) → z = 1) :
    Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* (↥(barIn M K) ⧸ center ↥(barIn M K))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L : Subgroup (Mbar M) := barIn M K with hL
  set f : ↥K →* ↥L := toBar hKM with hf
  have hfs : Function.Surjective f := toBar_surjective hKM
  set φ : ↥K →* ↥L ⧸ center ↥L := (QuotientGroup.mk' (center ↥L)).comp f with hφdef
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hfs
  have hkerf : f.ker ≤ pPrimeCore 2 ↥K := by
    refine le_sSup ⟨MonoidHom.normal_ker f, ?_⟩
    have hle : f.ker.map (Subgroup.inclusion hKM) ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨k, hk, rfl⟩
      have h1 : f k = 1 := hk
      have h2 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hcard : Nat.card ↥(f.ker.map (Subgroup.inclusion hKM)) = Nat.card ↥f.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKM)
    rw [← hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have hker : φ.ker = pPrimeCore 2 ↥K := by
    apply le_antisymm
    · intro k hk
      have hfk : f k ∈ center ↥L := by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hk
        exact hk
      have hcen : ∀ g : ↥K ⧸ pPrimeCore 2 ↥K,
          g * (QuotientGroup.mk k : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk k * g := by
        intro g
        obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective g
        have h1 : f (k' * k) = f (k * k') := by
          rw [map_mul, map_mul]
          exact Subgroup.mem_center_iff.mp hfk (f k')
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        apply hkerf
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff k).mp (hZ _ hcen)
    · have hN : ((pPrimeCore 2 ↥K).map f).Normal := (pPrimeCore_normal (p := 2)).map f hfs
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hle
      · exfalso
        have hodd : Odd (Nat.card ↥L) := by
          have h1 : Nat.card ↥L = Nat.card ↥((pPrimeCore 2 ↥K).map f) := by
            rw [htop, Subgroup.card_top]
          rw [h1]
          exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right
            (Subgroup.card_map_dvd (pPrimeCore 2 ↥K) f)
            (pPrimeCore_coprime_card (p := 2) (G := ↥K)))
        have hsol : Group.IsSolvable ↥L := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
        have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
        have : Group.IsPerfect ↥L := hq.1
        exact Group.IsPerfect.not_isSolvable ↥L hsol
      · intro k hk
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact hle ⟨k, hk, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

omit [Finite G] in
theorem barIn_le_normalizer {M K A : Subgroup G} (hKM : K ≤ M)
    (hA : ∀ a ∈ A, a ∈ normalizer (K : Set G)) :
    barIn M A ≤ normalizer (barIn M K : Set (Mbar M)) := by
  have h1 : A.subgroupOf M ≤ normalizer ((K.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hKM]
    intro a ha
    exact Subgroup.mem_subgroupOf.2 (hA _ (Subgroup.mem_subgroupOf.1 ha))
  exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)

end S3T2

open S3T2

theorem loc28_of_b2 (hB2 : B_B2_g4) {G : Type} [Group G] [Finite G] :
    ∀ (x : G) (K A B M : Subgroup G), Hyp2 G → IsTwoTerminal x K →
      QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → IsSource2 x K A → IsExtSource2 x K A B →
      pRank 2 ↥B = 4 → M ≠ ⊤ → K ≤ M → gammaK 2 B 3 ≤ M →
        ∃ _hN : (A.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤
            normalizer (barIn M K : Set (Mbar M)),
          IsLocBal32 (↥(barIn M K) ⧸ center ↥(barIn M K))
            ((((A.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).subgroupOf
              (normalizer (barIn M K : Set (Mbar M)))).map (rhoL (barIn M K))) := by
  classical
  intro x K A B M hyp ht h3 hsrc hext hB4 hM hKM hΓ
  have hILo : IsILo 2 x K := ht.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hext.2.2.2.1
  have hBM : B ≤ M := (S3Boot152.le_gammaK_self hBel (by rw [hB4]; norm_num)).trans hΓ
  have hxM : x ∈ M := hBM hext.2.1
  have hAM : A ≤ M := hext.1.trans hBM
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h3
  obtain ⟨E, hEK, hAE, -, hEel, -, -⟩ : ∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧ x ∉ E ∧
      CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4 ∧
      (QShape3 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨
        QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) := by
    obtain ⟨-, -, -, hcase⟩ := hsrc
    rcases hcase with ⟨-, h1⟩ | h
    · exact (B1.PilotS3.not_qShape1_of_center_trivial h1 hZ).elim
    · exact h
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hxA : x ∈ A := hAE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxk : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm
  have hzk : ∀ y ∈ zpowers x, ∀ k ∈ K, y * k = k * y := by
    intro y hy k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (show Commute x k from hxk k hk) n)).eq
  have hAN : ∀ a ∈ A, a ∈ normalizer (K : Set G) := by
    have hle : A ≤ normalizer (K : Set G) := by
      rw [hAE]
      refine sup_le (hEK.trans Subgroup.le_normalizer) ?_
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer (K : Set G))
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hzk y hy k hk).symm
    exact fun a ha => hle ha
  set L : Subgroup (Mbar M) := barIn M K with hL
  set NL : Subgroup (Mbar M) := normalizer (L : Set (Mbar M)) with hNL
  have hN : (A.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤ NL :=
    barIn_le_normalizer hKM hAN
  refine ⟨hN, ?_⟩
  have hKc := B2.barIn_K_isCompIn_gen hB2 hyp hM hILo hKM hxM
  have hKq : IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKc.1) hKc.2.1
  obtain ⟨φ⟩ := exists_equiv_center_quot hKM hKq hZ
  have hQ3 : QShape3 (↥L ⧸ center ↥L) := qShape3_of_mulEquiv φ h3
  set Eb : Subgroup (Mbar M) := barIn M E with hEb
  have hEbL : Eb ≤ L := Subgroup.map_mono (Subgroup.comap_mono hEK)
  have hEbN : Eb ≤ NL := (Subgroup.map_mono (Subgroup.comap_mono hEA)).trans hN
  have hloc : IsLocBal32 (↥L ⧸ center ↥L) ((Eb.subgroupOf NL).map (rhoL L)) := by
    refine S1Lemma282Bal.locBal32_of_equiv L (MulEquiv.refl ↥L) (Ab := Eb.subgroupOf L)
      (fun B₀ hB₀ => ?_) hEbL
      (fun b hb => ⟨⟨b, hEbL hb⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩)
    set Ab' : Subgroup (↥L ⧸ center ↥L) :=
      (Eb.subgroupOf L).map (QuotientGroup.mk' (center ↥L)) with hAb'
    have h2 : ∀ b ∈ B₀.comap MulAut.conj ⊓ Ab', b * b = 1 := by
      rintro _ ⟨-, ⟨c, hc, rfl⟩⟩
      obtain ⟨e, he, hec⟩ := Subgroup.mem_subgroupOf.1 hc
      have he2 : (e : G) * e = 1 := by
        have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) (e : G)
          (Subgroup.mem_subgroupOf.1 he)
        rwa [sq] at this
      have hc2 : c * c = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, ← hec, ← map_mul]
        have : e * e = 1 := Subtype.ext he2
        rw [this, map_one]
        rfl
      rw [← map_mul, hc2, map_one]
    have h3' := locBal32_L3_gen hQ3 (B₀.comap MulAut.conj ⊓ Ab') h2
    have hBB : (B₀.comap MulAut.conj ⊓ Ab').map MulAut.conj = B₀ := by
      apply le_antisymm
      · exact (Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le _ _)
      · intro b hb
        obtain ⟨a, ha, rfl⟩ := hB₀ hb
        exact ⟨a, ⟨hb, ha⟩, rfl⟩
    rwa [hBB] at h3'
  have hEnorm : E ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hzk y hy e (hEK he)
  have himg : (((A.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).subgroupOf NL).map
      (rhoL L) = (Eb.subgroupOf NL).map (rhoL L) := by
    apply le_antisymm
    · rintro _ ⟨n, hn, rfl⟩
      obtain ⟨a, ha, han⟩ := Subgroup.mem_subgroupOf.1 hn
      have haA : (a : G) ∈ ((E ⊔ zpowers x : Subgroup G) : Set G) := by
        rw [← hAE]
        exact Subgroup.mem_subgroupOf.1 ha
      rw [Subgroup.coe_mul_of_left_le_normalizer_right E (zpowers x) hEnorm] at haA
      obtain ⟨e, he, y, hy, hey⟩ := haA
      have heM : e ∈ M := hKM (hEK he)
      have hyA : y ∈ A := hAE ▸ Subgroup.mem_sup_right hy
      have hyM : y ∈ M := hAM hyA
      have heN : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨e, heM⟩ ∈ NL :=
        hEbN ⟨⟨e, heM⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      have hyN : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨y, hyM⟩ ∈ NL :=
        hN ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.2 hyA, rfl⟩
      have hnn : n = ⟨_, heN⟩ * ⟨_, hyN⟩ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, ← map_mul, ← han]
        congr 1
        exact Subtype.ext hey.symm
      have h0 : CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom L ⟨_, hyN⟩ = 1 := by
        refine MulEquiv.ext fun l => Subtype.ext ?_
        rw [CFSG.LocalAnalysis.ComponentInitial.coe_normalizerConjHom_apply, MulAut.one_apply]
        obtain ⟨m, hm, hml⟩ := l.2
        rw [← hml, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hzk y hy (m : G) (Subgroup.mem_subgroupOf.1 hm), mul_inv_cancel_right]
      have hy1 : rhoL L ⟨_, hyN⟩ = 1 := by
        simp only [rhoL, MonoidHom.comp_apply, h0, map_one]
      refine ⟨⟨_, heN⟩, Subgroup.mem_subgroupOf.2 ⟨⟨e, heM⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩,
        ?_⟩
      rw [hnn, map_mul, hy1, mul_one]
    · exact Subgroup.map_mono (Subgroup.comap_mono (Subgroup.map_mono (Subgroup.comap_mono hEA)))
  rw [himg]
  exact hloc

end CFSG.GH74.Generic.BProg.B3
