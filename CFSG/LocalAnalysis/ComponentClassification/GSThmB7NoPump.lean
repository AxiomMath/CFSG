module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NPMatch
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Cor
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsic
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped MatrixGroups

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem normal_layerIn_subgroupOf (Y : Subgroup X) :
    ((layerIn Y).subgroupOf Y).Normal := by
  have hc : (pLayer ↥Y 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  have heq : (layerIn Y).subgroupOf Y = pLayer ↥Y 2 :=
    comap_map_eq_self_of_injective Y.subtype_injective _
  rw [heq]
  infer_instance

theorem Setting.exists_sl2_inf_of_isSubnormal (hConj : CFSp4Conj) (hComp : CFSp4Comp)
    (hOut : CFSp4Outer) (hCent : CFL2Cent) (s : Setting X)
    (hNS : normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X)) {b : X}
    (hb : Lemma61Case2 s.h s.y b)
    (hLb : ((Lay s.h s.y).subgroupOf (centralizer ({b} : Set X))).IsSubnormal)
    {z : X} (hzD : z ∈ s.h.D) (hzS : ∀ t ∈ s.h.S, t * z = z * t) (hz2 : orderOf z = 2) :
    ∃ N : Subgroup X, N ≤ centralizer ({b} : Set X) ⊓ centralizer ({s.h.a * b * z} : Set X) ∧
      IsPComponent 2 (N.subgroupOf (centralizer ({b} : Set X) ⊓
        centralizer ({s.h.a * b * z} : Set X))) ∧ s.h.a * b * z ∈ N ∧
      ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) := by
  set d := s.toData hConj hComp hOut hCent with hd
  obtain ⟨hb1, hbx, hb3, hb4, hb5, hb6, hb7⟩ := hb
  have hb' : d.Case2 b := ⟨hb1, hbx, hb3, hb4, hb5, hb6, hb7⟩
  have hbB0 : b ∈ B0 s.h s.y := hb4
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have habz : s.h.a * b * z = z * (s.h.a * b) := Setting.commute_z hzS hbB0
  have hzP : z ∉ s.h.P := by
    intro hzP
    have : z ∈ s.h.D ⊓ s.h.P := mem_inf.mpr ⟨hzD, hzP⟩
    rw [s.h.D_inf_P_eq_bot s.hZJ, mem_bot] at this
    exact hz1 this
  have habP : s.h.a * b ∈ s.h.P := mul_mem s.h.a_mem_P hb'.b_mem_P
  have hzab : z ≠ s.h.a * b := fun h => hzP (h ▸ habP)
  have habL := hb'.ab_mem_L hNS
  rw [hd, Setting.toData_h, Setting.toData_y] at habL
  have hab2 := hb'.ab_mul_ab
  have hab1 := hb'.ab_ne_one
  rw [hd, Setting.toData_h] at hab2 hab1
  obtain ⟨N, hNX, hNpc, habzN, p', n, hp', hp'2, hn, ⟨eN⟩⟩ :=
    exists_sl2_of_cf hComp s.hp' s.hp2' s.hf' s.hLLie habL hab2 hab1 hzz
      hz1 habz hzab s.J0_le_L (Setting.J0_le_centralizer_ac hbB0)
      (s.L_inf_centralizer_le hbB0) s.isPComponent_J0 (s.mem_J0 hzD hzS hz2)
  have hLbC : Lay s.h s.y ≤ centralizer ({b} : Set X) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (s.L_le_centralizer hw) b
      hbB0).symm)
  exact ⟨N, le_inf (hNX.trans (inf_le_left.trans hLbC)) (hNX.trans inf_le_right),
    isPComponent_inf_of_isSubnormal hLbC hLb hNX hNpc, habzN, p', n, hp', hp'2, hn, ⟨eN⟩⟩

theorem Setting.exists_classical_of_sl2_inf (hS : SchreierFor Blueprint.Catalog)
    (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer) (hCent : CFL2Cent)
    [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X) (s : Setting X)
    (hNS : normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X)) {b : X}
    (hb : Lemma61Case2 s.h s.y b)
    (hW : ∀ z : X, z ∈ s.h.D → (∀ t ∈ s.h.S, t * z = z * t) → orderOf z = 2 →
      ∃ N : Subgroup X, N ≤ centralizer ({b} : Set X) ⊓ centralizer ({s.h.a * b * z} : Set X) ∧
        IsPComponent 2 (N.subgroupOf (centralizer ({b} : Set X) ⊓
          centralizer ({s.h.a * b * z} : Set X))) ∧ s.h.a * b * z ∈ N ∧
        ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
          Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n))) :
    ∃ (δ : X) (J' : Subgroup X), orderOf δ = 2 ∧ J' ≤ centralizer ({δ} : Set X) ∧
      IsPComponent 2 (J'.subgroupOf (centralizer ({δ} : Set X))) ∧ δ ∈ J' ∧
      CFSG.pRank 2 J' ≤ 1 ∧ Open.classicalInvolutionWitness J' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set d := s.toData hConj hComp hOut hCent with hd
  obtain ⟨hb1, hbx, hb3, hb4, hb5, hb6, hb7⟩ := hb
  have hb' : d.Case2 b := ⟨hb1, hbx, hb3, hb4, hb5, hb6, hb7⟩
  obtain ⟨r, -, -, hr1, hr2, hrb⟩ := hb'.exists_r hNS
  have hr1' : r⁻¹ * (s.h.a * b) * r = d.z := hr1
  have hr2' : r⁻¹ * d.z * r = s.h.a * b := hr2
  have hrb' : r⁻¹ * b * r = b := by rw [mul_assoc, ← hrb, ← mul_assoc, inv_mul_cancel, one_mul]
  have haS : s.h.a ∈ s.h.S := s.h.a_mem_S
  have hxS : s.h.x ∈ s.h.S := s.h.x_mem
  have hxa : s.h.x⁻¹ * s.h.a * s.h.x = s.h.a := by
    rw [mul_assoc, ← s.h.comm_a hxS, ← mul_assoc, inv_mul_cancel, one_mul]
  have hzS : ∀ t ∈ s.h.S, t * d.z = d.z * t := d.hzS
  have hxz : s.h.x⁻¹ * d.z * s.h.x = d.z := by
    rw [mul_assoc, ← hzS _ hxS, ← mul_assoc, inv_mul_cancel, one_mul]
  have hbB0 : b ∈ B0 s.h s.y := hb4
  have hbb : b * b = 1 := hb'.b_mul_b
  have habz : s.h.a * b * d.z = d.z * (s.h.a * b) := Setting.commute_z hzS hbB0
  have hga : (r * s.h.x)⁻¹ * s.h.a * (r * s.h.x) = s.h.a * b * d.z := by
    calc (r * s.h.x)⁻¹ * s.h.a * (r * s.h.x)
        = s.h.x⁻¹ * ((r⁻¹ * (s.h.a * b) * r) * (r⁻¹ * b * r)) * s.h.x := by
          rw [show (r⁻¹ * (s.h.a * b) * r) * (r⁻¹ * b * r) = r⁻¹ * (s.h.a * (b * b)) * r by
            group, hbb, mul_one]
          group
      _ = (s.h.x⁻¹ * d.z * s.h.x) * (s.h.x⁻¹ * b * s.h.x) := by rw [hr1', hrb']; group
      _ = s.h.a * b * d.z := by rw [hxz, hbx, habz]
  have hgz : (r * s.h.x)⁻¹ * d.z * (r * s.h.x) = b := by
    calc (r * s.h.x)⁻¹ * d.z * (r * s.h.x) = s.h.x⁻¹ * (r⁻¹ * d.z * r) * s.h.x := by group
      _ = (s.h.x⁻¹ * s.h.a * s.h.x) * (s.h.x⁻¹ * b * s.h.x) := by rw [hr2']; group
      _ = b := by rw [hxa, hbx, ← mul_assoc, s.a_mul_a, one_mul]
  obtain ⟨N, hNbX, hN1, habzN, p', n, hp', hp'2, hn, ⟨eN⟩⟩ := hW d.z d.hzD hzS d.hz2
  set φ : X ≃* X := MulAut.conj (r * s.h.x) with hφ
  have hφa : φ (s.h.a * b * d.z) = s.h.a := by
    rw [hφ, MulAut.conj_apply, ← hga]
    group
  have hφb : φ b = d.z := by
    rw [hφ, MulAut.conj_apply, ← hgz]
    group
  have hCmap : (centralizer ({b} : Set X) ⊓ centralizer ({s.h.a * b * d.z} : Set X)).map
      φ.toMonoidHom = centralizer ({s.h.a} : Set X) ⊓ centralizer ({d.z} : Set X) := by
    rw [Subgroup.map_inf _ _ _ φ.injective, CatFactsSp4.map_centralizer_singleton,
      CatFactsSp4.map_centralizer_singleton, hφa, hφb, inf_comm]
  have hN'pc : IsPComponent 2 ((N.map φ.toMonoidHom).subgroupOf (centralizer ({s.h.a} : Set X) ⊓
      centralizer ({d.z} : Set X))) := by
    have h1 := CatFactsSp4.isPComponent_map_subgroupOf 2 φ hNbX hN1
    rwa [hCmap] at h1
  have hN'X : N.map φ.toMonoidHom ≤ centralizer ({s.h.a} : Set X) ⊓
      centralizer ({d.z} : Set X) := by
    rw [← hCmap]
    exact map_mono hNbX
  have haN' : s.h.a ∈ N.map φ.toMonoidHom := by
    rw [← hφa]
    exact mem_map_of_mem _ habzN
  have ha1 : s.h.a ≠ 1 := d.a_ne_one
  have hCa : centralizer ({s.h.a} : Set X) ≠ ⊤ := by
    intro htop
    apply ha1
    have hcen : s.h.a ∈ center X := by
      rw [mem_center_iff]
      intro w
      exact mem_centralizer_singleton_iff.mp (htop ▸ mem_top w)
    have hbot : center X = ⊥ := by
      rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨u, v, huv⟩ := hnonab
        exact huv ((mem_center_iff.mp (h1 ▸ mem_top v : v ∈ center X)) u)
    rw [hbot] at hcen
    exact mem_bot.mp hcen
  have hsch : LBalance.SchreierSections ↥(centralizer ({s.h.a} : Set X)) :=
    schreierSections_of_isKGroupCat hS (isKGroupCat_of_ne_top' hK hCa)
  have hzJ : d.z ∈ s.h.J := (mem_inf.mp d.hzD).2
  have hzC : d.z ∈ centralizer ({s.h.a} : Set X) := s.h.J_le hzJ
  have hN'L : N.map φ.toMonoidHom ≤ layerIn (centralizer ({s.h.a} : Set X)) := by
    have h1 := lBalancePLayer_inf_centralizer_le_of_sections (p := 2) hsch hzC
      ⟨1, by rw [pow_one, pow_two]; exact d.z_mul_z⟩
    rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
    refine le_trans ?_ h1
    have h2 : (N.map φ.toMonoidHom).subgroupOf (centralizer ({s.h.a} : Set X) ⊓
        centralizer ({d.z} : Set X)) ≤
        pLayer ↥(centralizer ({s.h.a} : Set X) ⊓ centralizer ({d.z} : Set X)) 2 :=
      le_sSup hN'pc
    have h3 := map_mono
      (f := (centralizer ({s.h.a} : Set X) ⊓ centralizer ({d.z} : Set X)).subtype) h2
    rwa [map_subgroupOf_eq_of_le hN'X] at h3
  have haJ : s.h.a ∉ s.h.J := by
    intro haJ
    have h1 : s.h.a ∈ s.h.D ⊓ s.h.P := mem_inf.mpr ⟨mem_inf.mpr ⟨haS, haJ⟩, s.h.a_mem_P⟩
    have hDP : s.h.D ⊓ s.h.P = ⊥ := d.hDP
    rw [hDP, mem_bot] at h1
    exact ha1 h1
  obtain ⟨M, hMC, hMpc, -, haM, ⟨eM⟩⟩ := exists_isPComponent_of_isPComponent_inf s.h.J_le
    s.h.isPComponent_J s.hJn hzJ d.z_mul_z hN'X hN'pc hN'L haN' s.h.J_le s.a_mul_a haJ
  let e₀ : ↥(N.map φ.toMonoidHom) ≃* ↥N :=
    (N.equivMapOfInjective φ.toMonoidHom φ.injective).symm
  let e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, GaloisField p' n) :=
    eM.symm.trans ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₀).trans eN)
  have hchar : ringChar (GaloisField p' n) ≠ 2 := by
    rw [ringChar.eq (GaloisField p' n) p']
    exact hp'2
  have hrank : CFSG.pRank 2 M ≤ 1 := by
    have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 M) := fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
    rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd,
      UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two e]
    exact TBLit.pRank_two_SL2_le_one hchar
  refine ⟨s.h.a, M, s.h.orderOf_a, hMC, hMpc, haM, hrank, ?_⟩
  exact .inl ⟨p', n, hp', hp'2, hn,
    ⟨(QuotientGroup.quotientMulEquivOfEq (TBLit.classicalInvolutionOddCore_eq M)).trans e⟩⟩

end Seven

@[expose] def WeakNoPumpStatement71 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J → h.Table517 → conjugate h.K h.a ≠ h.K →
      ∀ s : Seven.Setting X, h.IsX0Min s.y → Seven.Prop62Output h s.h s.y →
      normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) →
      ∀ b : X, Seven.Lemma61Case2 s.h s.y b →
      ∀ z : X, z ∈ s.h.D → (∀ t ∈ s.h.S, t * z = z * t) → orderOf z = 2 →
      ∃ N : Subgroup X, N ≤ centralizer ({b} : Set X) ⊓ centralizer ({s.h.a * b * z} : Set X) ∧
        IsPComponent 2 (N.subgroupOf (centralizer ({b} : Set X) ⊓
          centralizer ({s.h.a * b * z} : Set X))) ∧ s.h.a * b * z ∈ N ∧
        ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
          Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n))

theorem classicalInvolutionStatement71_of_weakNoPump (hS : SchreierFor Blueprint.Catalog)
    (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer) (hCent : CFL2Cent)
    (hW : WeakNoPumpStatement71) : ClassicalInvolutionStatement71 := by
  intro X _ _ _ hnonab hK hz hU h hmax hiso hnB1 hnB2a hTab hKa s hy hrel hNS b hb
  exact s.exists_classical_of_sl2_inf hS hConj hComp hOut hCent hnonab hK hNS hb
    (hW X hnonab hK hz hU h hmax hiso hnB1 hnB2a hTab hKa s hy hrel hNS b hb)

end CFSG.ComponentClassification.GSThmB
