module

public import CFSG.GH74.GLS.Prop27.Defs
public import CFSG.GH74.GLS.Prop27.EndGame
public import CFSG.GH74.Uniqueness.Bender.Aut

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup CFSG.GH74.E2 CFSG.GH74.Uniqueness.Bender

theorem locBal2_of_benderType_suzuki
    (Pred : ∀ (S : Type) [Group S], Prop)
    (hP : ∀ (S : Type) [Group S], Pred S → ∃ n : ℕ, BenderType S n 2 1) : LocBal2 Pred := by
  intro X _ _ N hN hPred hC e0 he0
  have hNn : N.Normal := hN
  obtain ⟨n, hBT⟩ := hP ↥N hPred
  have he02 : e0 * e0 = 1 := by
    have h1 := pow_orderOf_eq_one e0
    rwa [he0, sq] at h1
  have he01 : e0 ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at he0
    omega
  have hcent_eq : ∀ (x : X) (v : ↥N), (∀ k : ↥N, (MulAut.conjNormal (H := N) x) k = v * k * v⁻¹) →
      x = (v : X) := by
    intro x v hxv
    have hcen : (v : X)⁻¹ * x ∈ Subgroup.centralizer (N : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h1 := congrArg Subtype.val (hxv ⟨m, hm⟩)
      simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc m * ((v : X)⁻¹ * x) = (v : X)⁻¹ * ((v : X) * m * (v : X)⁻¹) * x := by group
        _ = (v : X)⁻¹ * (x * m * x⁻¹) * x := by rw [h1]
        _ = (v : X)⁻¹ * x * m := by group
    rw [hC, Subgroup.mem_bot] at hcen
    calc x = (v : X) * ((v : X)⁻¹ * x) := by group
      _ = (v : X) := by rw [hcen, mul_one]
  have hsq : (MulAut.conjNormal (H := N) e0) * (MulAut.conjNormal (H := N) e0) = 1 := by
    rw [← map_mul, he02, map_one]
  obtain ⟨v, -, hσv⟩ := hBT.exists_inner_of_sq_eq_one_suzuki _ hsq
  have he0eq : e0 = (v : X) := hcent_eq e0 v hσv
  have hmemN : e0 ∈ N := he0eq ▸ v.2
  obtain ⟨t, hc⟩ := hBT.exists_benderCore (default : Sylow 2 ↥N)
  set Q : Sylow 2 ↥N := default with hQ
  have hu2 : (⟨e0, hmemN⟩ : ↥N) * ⟨e0, hmemN⟩ = 1 := Subtype.ext he02
  have hu1 : (⟨e0, hmemN⟩ : ↥N) ≠ 1 := fun h => he01 (congrArg Subtype.val h)
  have key : ∀ z : ↥N, z ∈ rootCenter (Q : Subgroup ↥N) → z ≠ 1 →
      pPrimeCore 2 ↥(centralizer ({(z : X)} : Set X)) = ⊥ := by
    intro z hz hz1
    have hcz : centralizer ({z} : Set ↥N) = (Q : Subgroup ↥N) :=
      hc.centralizer_eq_of_e_one hz hz1
    have hQ2 : IsPGroup 2 (Q : Subgroup ↥N) := Q.isPGroup'
    have hmemQ : ∀ q : ↥N, q ∈ (Q : Subgroup ↥N) ↔ (q : X) * (z : X) = (z : X) * (q : X) := by
      intro q
      rw [← hcz, Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    apply pPrimeCore_two_eq_bot_of_forall
    intro N0 hN0C hN0n hodd
    have hNodd : ∀ x ∈ N0, Odd (orderOf x) := fun x hx =>
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N0 hx)
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxz : x * (z : X) = (z : X) * x := Subgroup.mem_centralizer_singleton_iff.mp (hN0C hx)
    have hxz' : x⁻¹ * (z : X) = (z : X) * x⁻¹ := by
      calc x⁻¹ * (z : X) = x⁻¹ * ((z : X) * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * (z : X)) * x⁻¹ := by rw [hxz]
        _ = (z : X) * x⁻¹ := by group
    have hσQ : ∀ q ∈ (Q : Subgroup ↥N), (MulAut.conjNormal (H := N) x) q = q := by
      intro q hq
      have hqz := (hmemQ q).mp hq
      have hqC : (q : X) ∈ centralizer ({(z : X)} : Set X) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hqz
      have hxq : (MulAut.conjNormal (H := N) x) q ∈ (Q : Subgroup ↥N) := by
        rw [hmemQ]
        simp only [MulAut.conjNormal_apply]
        calc (x * (q : X) * x⁻¹) * (z : X) = x * (q : X) * (x⁻¹ * (z : X)) := by group
          _ = x * (q : X) * ((z : X) * x⁻¹) := by rw [hxz']
          _ = x * ((q : X) * (z : X)) * x⁻¹ := by group
          _ = x * ((z : X) * (q : X)) * x⁻¹ := by rw [hqz]
          _ = (x * (z : X)) * (q : X) * x⁻¹ := by group
          _ = ((z : X) * x) * (q : X) * x⁻¹ := by rw [hxz]
          _ = (z : X) * (x * (q : X) * x⁻¹) := by group
      have hw : (q : X) * x⁻¹ * (q : X)⁻¹ ∈ N0 := hN0n _ hqC x⁻¹ (N0.inv_mem hx)
      have hy : x * ((q : X) * x⁻¹ * (q : X)⁻¹) ∈ N0 := N0.mul_mem hx hw
      have hyQ : (MulAut.conjNormal (H := N) x) q * q⁻¹ ∈ (Q : Subgroup ↥N) :=
        Q.mul_mem hxq (Q.inv_mem hq)
      have hyeq : (((MulAut.conjNormal (H := N) x) q * q⁻¹ : ↥N) : X) =
          x * ((q : X) * x⁻¹ * (q : X)⁻¹) := by
        simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hodd' : Odd (orderOf ((MulAut.conjNormal (H := N) x) q * q⁻¹)) := by
        rw [← Subgroup.orderOf_coe, hyeq]
        exact hNodd _ hy
      have h1 := eq_one_of_isPGroup_two_of_odd_orderOf hQ2 hyQ hodd'
      exact mul_inv_eq_one.mp h1
    obtain ⟨r, hrZ, hr⟩ := hBT.lemma_3_6_a Q (MulAut.conjNormal (H := N) x) hσQ
    have hxr : x = (r : X) := hcent_eq x r hr
    have hrQ : r ∈ (Q : Subgroup ↥N) := rootCenter_le _ hrZ
    have hodd'' : Odd (orderOf r) := by
      rw [← Subgroup.orderOf_coe, ← hxr]
      exact hNodd x hx
    have hr1 := eq_one_of_isPGroup_two_of_odd_orderOf hQ2 hrQ hodd''
    rw [hxr, hr1]
    rfl
  obtain ⟨g, hg, hg1⟩ := hc.exists_conj_rootCenter hu2 hu1
  refine pPrimeCore_centralizer_eq_bot_of_mulEquiv (MulAut.conj ((g : X)⁻¹)) ?_
  have hconj : (MulAut.conj ((g : X)⁻¹) : MulAut X) e0 =
      (((g⁻¹ * ⟨e0, hmemN⟩ * g : ↥N)) : X) := by
    simp
  rw [hconj]
  exact key _ hg hg1

theorem benderType_of_shapeSz8 {S : Type} [Group S] (h : ShapeSz8 S) : BenderType S 3 2 1 := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · obtain ⟨-, a, ha, F, _, _, hf, hF, ⟨e⟩⟩ := hS
    have ha1 : a = 1 := by omega
    subst ha1
    have hF' : Nat.card F = 2 ^ (2 * 1 + 1) := by simpa using hF
    exact BenderType.suzuki 1 le_rfl (e.trans
      ((CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hF').trans
        (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup 1).symm)))

theorem locBal2_Sz8_bender : LocBal2 ShapeSz8 :=
  locBal2_of_benderType_suzuki ShapeSz8 (fun _ _ h => ⟨3, benderType_of_shapeSz8 h⟩)

end CFSG.GH74.GLS.Prop27
