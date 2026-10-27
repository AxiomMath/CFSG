module

public import CFSG.Quasithin.H13.A6S1372L76N3o
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76N3l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Y

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem L1_le_of_natSL32_F4 (h139 : Stmt13_3_9_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (hNS : ¬ LieModel G .PSp 3 2 1) {H : Subgroup G} (hH : H ∈ S.Hz)
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H)
    (D : A6L76N3.NatReal (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
    (hc : ∃ x ∈ S.X1375, ∃ hxH : x ∈ H, ∃ y ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)),
      A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) ⟨x, hxH⟩ * y ≠
        y * A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) ⟨x, hxH⟩) :
    S.L1 ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have P := S.plusData_X1375
  have hXN : S.X1375 ≤ H ⊓ Subgroup.normalizer (K : Set G) :=
    le_inf (X1375_le_H hH) (X1375_le_normalizer h38 hH hK)
  have hKN : K ≤ H ⊓ Subgroup.normalizer (K : Set G) := le_inf hKH Subgroup.le_normalizer
  obtain ⟨σ, hσdef⟩ : ∃ f, f = S.secActN hH hK := ⟨_, rfl⟩
  have hσcoe : ∀ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)),
      (σ n).1 = A6Mod.secAct hHU hHV ⟨n, n.2.1⟩ := fun n => by subst hσdef; rfl
  obtain ⟨φ, hφdef⟩ : ∃ f, f = D.phiN.comp σ := ⟨_, rfl⟩
  have hφapp : ∀ n, φ n = D.phiN (σ n) := fun n => by subst hφdef; rfl
  obtain ⟨ψ, hψdef⟩ : ∃ f, f = D.cN.comp σ := ⟨_, rfl⟩
  have hψapp : ∀ n, ψ n = D.cN (σ n) := fun n => by subst hψdef; rfl

  have hσK : ∀ (k : G) (hk : k ∈ K), σ ⟨k, hKN hk⟩ = A6L76N3.incY
      ⟨_, (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩⟩ :=
    fun k hk => Subtype.ext (hσcoe _)
  have hψK : ∀ (k : G) (hk : k ∈ K), ψ ⟨k, hKN hk⟩ = 1 := fun k hk => by
    rw [hψapp, hσK k hk]
    exact D.cN_incY _
  have hQ : ∀ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)), σ n = 1 →
      (n : G) ∈ pCoreOf 2 H := fun n hn =>
    (S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH n.2.1).2
      ((A6Mod.secAct_eq_one_iff hHU hHV _).1 ((hσcoe n).symm.trans (congrArg Subtype.val hn)))
  have hφ1 : ∀ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)), φ n = 1 → ∀ k ∈ K,
      (n : G) * k * (n : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    intro n hn k hk
    have hc2 : σ n * σ ⟨k, hKN hk⟩ = σ ⟨k, hKN hk⟩ * σ n := by
      rw [hσK k hk]
      exact Subtype.ext (D.comm_of_phiN_eq_one (n := σ n) ((hφapp n).symm.trans hn)
        ⟨_, (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩⟩)
    refine hQ (n * ⟨k, hKN hk⟩ * n⁻¹ * ⟨k, hKN hk⟩⁻¹) ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc2]
    group

  obtain ⟨x₀, hx₀X, hx₀ρ, hx₀3⟩ := S.exists_X1375_c012_cube
  obtain ⟨x₀N, hx₀N⟩ : ∃ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (n : G) = x₀ :=
    ⟨⟨x₀, hXN hx₀X⟩, rfl⟩
  have hx₀N3 : x₀N ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hx₀N]; exact hx₀3)
  have hx₀NX : (x₀N : G) ∈ S.X1375 := by rw [hx₀N]; exact hx₀X

  have hdec : ∀ n : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (n : G) ∈ S.X1375 →
      ∃ i : ℕ, i < 3 ∧ ∃ j : ℕ, (x₀N ^ i * n) ^ 2 ^ j = 1 := by
    intro n hn
    have h2 : ∀ y : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (y : G) ∈ pCoreOf 2 S.X1375 →
        ∃ j : ℕ, y ^ 2 ^ j = 1 := by
      intro y hy
      obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 S.X1375 ⟨(y : G), hy⟩
      exact ⟨j, Subtype.ext (by simpa using congrArg Subtype.val hj)⟩
    rcases S.X1375_decomp hx₀X hx₀ρ hn with h | h | h
    · obtain ⟨j, hj⟩ := h2 n h
      exact ⟨0, by norm_num, j, by rw [pow_zero, one_mul]; exact hj⟩
    · refine ⟨2, by norm_num, h2 _ ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_pow, hx₀N, pow_two]
      exact h
    · refine ⟨1, by norm_num, h2 _ ?_⟩
      rw [Subgroup.coe_mul, pow_one, hx₀N]
      exact h

  have hpowodd : ∀ (x : G) (hx : x ∈ H ⊓ Subgroup.normalizer (K : Set G)),
      (⟨x, hx⟩ : ↥(H ⊓ Subgroup.normalizer (K : Set G))) ^ orderOf x = 1 :=
    fun x hx => Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one x)

  have ha1 : φ x₀N ≠ 1 := by
    intro ha1
    have hle : S.X1375 ≤ (φ.ker).map (H ⊓ Subgroup.normalizer (K : Set G)).subtype := by
      refine (X1375_le_oTwoUpper (S := S)).trans ((Subgroup.closure_le _).2 ?_)
      rintro x ⟨hx, hxo⟩
      obtain ⟨i, -, j, hj⟩ := hdec ⟨x, hXN hx⟩ hx
      exact ⟨⟨x, hXN hx⟩, MonoidHom.mem_ker.2 (A6L76N3.eq_one_of_dec φ ha1 hj
        (hpowodd x (hXN hx)) hxo), rfl⟩
    obtain ⟨x, hxX, hxH, y, hy, hne⟩ := hc
    apply hne
    obtain ⟨n, hn, hnx⟩ := hle hxX
    have e : n = ⟨x, hXN hxX⟩ := Subtype.ext hnx
    rw [e] at hn
    have h := D.comm_of_phiN_eq_one (n := σ ⟨x, hXN hxX⟩)
      ((hφapp _).symm.trans (MonoidHom.mem_ker.1 hn)) ⟨y, hy⟩
    rw [hσcoe] at h
    exact h

  obtain ⟨φK, hφKdef⟩ : ∃ f : ↥K →* SL3.S, f = φ.comp (Subgroup.inclusion hKN) := ⟨_, rfl⟩
  have hφK : Function.Surjective φK := by
    intro A
    obtain ⟨y, hy⟩ := D.phiY_bijective.2 A
    obtain ⟨f, hfK, hf⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 y.2
    refine ⟨⟨(f : G), hfK⟩, ?_⟩
    have e : σ (Subgroup.inclusion hKN ⟨(f : G), hfK⟩) = A6L76N3.incY y :=
      Subtype.ext ((hσcoe _).trans hf)
    rw [hφKdef, MonoidHom.comp_apply, hφapp, e]
    exact hy
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hsyl := S153D.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hK) hTs
  have hP2 : IsPGroup 2 ↥(((T ⊓ K).subgroupOf K).map φK) :=
    (hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm).map φK
  have hPodd : ¬ 2 ∣ (((T ⊓ K).subgroupOf K).map φK).index := fun hd =>
    hsyl.2.2 (hd.trans (Subgroup.index_map_dvd _ hφK))
  obtain ⟨g, hg⟩ := A6L76N3.exists_conj_P0 hP2 hPodd
  have hga : ∀ q ∈ SL3.P0, ∃ t ∈ {n : ↥(H ⊓ Subgroup.normalizer (K : Set G)) | (n : G) ∈ T ⊓ K},
      φ t = g⁻¹ * q * g := by
    intro q hq
    obtain ⟨t', ht', hteq⟩ := hg q hq
    rw [hφKdef, MonoidHom.comp_apply] at hteq
    exact ⟨Subgroup.inclusion hKN t', Subgroup.mem_subgroupOf.1 ht', hteq⟩
  have hmX : ∀ t : ↥(H ⊓ Subgroup.normalizer (K : Set G)), (t : G) ∈ T ⊓ K →
      ((t * x₀N * t⁻¹ * x₀N⁻¹ : ↥(H ⊓ Subgroup.normalizer (K : Set G))) : G) ∈ S.X1375 := by
    intro t ht
    show (t : G) * x₀N * (t : G)⁻¹ * (x₀N : G)⁻¹ ∈ S.X1375
    exact S.X1375.mul_mem ((Subgroup.mem_normalizer_iff.mp (P.T_le ht.1) _).mp hx₀NX)
      (S.X1375.inv_mem hx₀NX)

  have hc1 : ψ x₀N = 1 := A6L76N3.eq_one_of_comm_P0 φ ψ hx₀N3 ha1
    (fun t ht => hψK t ht.2) (fun t ht => hdec _ (hmX t ht)) hga

  have hXK : S.X1375 ≤ K := by
    refine (X1375_le_oTwoUpper (S := S)).trans ((Subgroup.closure_le _).2 ?_)
    rintro x ⟨hx, hxo⟩
    obtain ⟨i, -, j, hj⟩ := hdec ⟨x, hXN hx⟩ hx
    have hψx := A6L76N3.eq_one_of_dec ψ hc1 hj (hpowodd x (hXN hx)) hxo
    have hmem := D.mem_of_cN_eq_one (n := σ ⟨x, hXN hx⟩) ((hψapp _).symm.trans hψx)
    obtain ⟨f, hfK, hf⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hmem
    have hfx : (f : G)⁻¹ * x ∈ H ⊓ Subgroup.normalizer (K : Set G) :=
      (H ⊓ Subgroup.normalizer (K : Set G)).mul_mem (Subgroup.inv_mem _ (hKN hfK)) (hXN hx)
    have hq : (f : G)⁻¹ * x ∈ pCoreOf 2 H := by
      refine hQ ⟨_, hfx⟩ (Subtype.ext ?_)
      rw [hσcoe]
      show A6Mod.secAct hHU hHV ⟨(f : G)⁻¹ * x, hfx.1⟩ = 1
      have e : (⟨(f : G)⁻¹ * x, hfx.1⟩ : ↥H) = f⁻¹ * ⟨x, (hXN hx).1⟩ := Subtype.ext rfl
      rw [e, map_mul, map_inv, hf, hσcoe]
      exact inv_mul_cancel _
    have h4 := A6L76N3.mem_of_odd_of_mul_QH hK hfK hq (by rwa [mul_inv_cancel_left])
    rwa [mul_inv_cancel_left] at h4

  by_contra hL1K
  have : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    A6L76A.isSimpleGroup_statedSL (le_refl 3) (by simp)
  have : Nontrivial SL3.S := ⟨⟨SL3.s1, 1, by decide⟩⟩
  have : Nontrivial ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := D.phiYEquiv.toEquiv.nontrivial
  have hrad := A6L76A.rad_eq_bot_of_surjective
    (A6L76A.not_isSolvable_statedSL (le_refl 3)) D.π D.surj
  exact S.lem1375_seven_F4 h139 h37 h38 hH hK hXK hL1K hrad
    (S.L1_le_sup_of_conj_P0 h38 hH hK φ (fun t ht => ht.1) hga hφ1 hx₀NX
      (by rw [← map_pow, hx₀N3, map_one]) ha1)

end Setting4

theorem lem1376OddNCL32_of_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) :
    Lem1376OddNCL32_F4 := by
  intro G _ _ T L V S hNS _ H hH _ _ K hK hSL hc
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSL
  obtain ⟨D⟩ := A6L76N3.nonempty_natReal (by rw [hF, pow_one]) hπ
  exact S.L1_le_of_natSL32_F4 h139 h37 h38 h13315 h1356two hNS hH hK D hc

theorem lem1376Full_holds_F4
    (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9_F4) (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (h1337 : Stmt13_3_7_F4) : Lem1376Full_F4 :=
  lem1376Full_of_l32_F4 (lem1376OddNCL32_of_F4 h139 h37 h38 h13315 h1356two) hF h36 h37 h38 h139
    h13314 h13315 h1356two h1337

end CFSG.Quasithin.H13.A6
