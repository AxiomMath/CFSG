module

public import CFSG.ClassicalInvolution.Asc77.AscS24BHyp
public import CFSG.ClassicalInvolution.Asc77.AscS24Alpha2
public import CFSG.ClassicalInvolution.Asc77.AscT7AEnd

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem isElemAbelian2_conjSub {A : Subgroup G} (hA : IsElemAbelian2 A 2) (n : G) :
    IsElemAbelian2 (conjSub n A) 2 := by
  refine ⟨?_, fun x hx => ?_⟩
  · have hinj : Function.Injective (MulAut.conj n).toMonoidHom := (MulAut.conj n).injective
    rw [show conjSub n A = A.map (MulAut.conj n).toMonoidHom from rfl,
      Subgroup.card_map_of_injective hinj]
    exact hA.1
  · rw [mem_conjSub_iff] at hx
    have h := hA.2 _ hx
    calc x * x = n * ((n⁻¹ * x * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = 1 := by rw [h]; group

omit [Finite G] in
theorem normalizer_alpha {B α₀ A₀ : Subgroup G}
    (halpha : ∀ A : Subgroup G, A ≤ B → IsElemAbelian2 A 2 → alphaOf A = α₀)
    (hA₀B : A₀ ≤ B) (hA₀ : IsElemAbelian2 A₀ 2) {n : G}
    (hn : n ∈ Subgroup.normalizer (B : Set G)) : n ∈ Subgroup.normalizer (α₀ : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  have hAB : conjSub n A₀ ≤ B := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * x * n)).mp (hA₀B hx)
    have : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    rwa [this] at h1
  have h1 := halpha _ hAB (isElemAbelian2_conjSub hA₀ n)
  rw [alphaOf_conjSub, halpha A₀ hA₀B hA₀] at h1
  exact h1

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

theorem mem_closure_of_mem_W {w : G} (hw : w ∈ W) (h2 : w * w = 1) :
    w ∈ Subgroup.closure ({C.D.F.j, z} : Set G) := by
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  rw [C.mul_nf] at h2
  obtain ⟨h1, h3⟩ := C.eq_one_of_nf _ _ h2
  have ha := C.four_dvd_of_x₁ h1
  have hb := C.four_dvd_of_x₃ h3
  obtain ⟨a', rfl⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
  have e1 : C.D.x₁ ^ (2 : ℤ) = z := by rw [zpow_two, ← sq, C.x₁_sq]
  have e3 : C.D.x₃ ^ (2 : ℤ) = C.D.F.j := by rw [zpow_two, ← sq, C.x₃_sq]
  rw [zpow_mul, zpow_mul, e1, e3]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem u_cases : u = C.D.F.j ∨ u = C.D.F.j * z := by
  obtain ⟨-, huW, hu2, hu1, huz⟩ := C.hd.hu
  rcases T7B.mem_closure_pair C.hjJ.sq C.hzK.sq C.hjJ.ne_one C.hzK.ne_one C.comm_jz
    (C.mem_closure_of_mem_W huW hu2) with h | h | h | h
  · exact absurd h hu1
  · exact Or.inl h
  · exact absurd h huz
  · exact Or.inr h

theorem r_conj_jz : C.D.F.ρ.r * (C.D.F.j * z) * C.D.F.ρ.r⁻¹ = C.D.F.j := by
  have hrz : C.D.F.ρ.r * z * C.D.F.ρ.r⁻¹ = z := by
    rw [(e189_commute_of_mem C.hzK C.r_mem_K).symm]; group
  calc C.D.F.ρ.r * (C.D.F.j * z) * C.D.F.ρ.r⁻¹
      = (C.D.F.ρ.r * C.D.F.j * C.D.F.ρ.r⁻¹) * (C.D.F.ρ.r * z * C.D.F.ρ.r⁻¹) := by group
    _ = C.D.F.j := by rw [C.r_conj_j, hrz, mul_assoc, C.hzK.sq, mul_one]

theorem r_mem_centralizer_z : C.D.F.ρ.r ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem C.hzK C.r_mem_K).symm

end Ctx8

namespace HCtx

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : HCtx p f Ω K K' W S R R' z u)

theorem T_card : Nat.card ↥H.T₃ = 2 * Nat.card ↥(Subgroup.zpowers H.C.D.x₃) := by
  rw [IsSylow2In.natCard_eq H.hT H.C.D.F.ρ₃.hRK]
  have h := Thompson.D_card H.C.D.c.hp H.C.D.c.hq H.C.D.c.hΩ H.C.D.c.hW H.C.D.F.ρ₃.hR
  rw [← H.C.D.h₃] at h
  exact h

theorem exists_s : ∃ s ∈ H.T₃, s ∉ Subgroup.zpowers H.C.D.x₃ := by
  by_contra hcon
  push Not at hcon
  have hle := Subgroup.card_le_of_le (fun y hy => hcon y hy : H.T₃ ≤ Subgroup.zpowers H.C.D.x₃)
  have hpos : 0 < Nat.card ↥(Subgroup.zpowers H.C.D.x₃) := Nat.card_pos
  have := H.T_card
  omega

theorem s_not_comm_z {s : G} (hs : s ∈ H.T₃) (hsU : s ∉ Subgroup.zpowers H.C.D.x₃) :
    s * z * s⁻¹ ≠ z := by
  intro h
  apply H.not_le_centralizer_z
  have hzs : z * s = s * z := by
    calc z * s = s * z * s⁻¹ * s := by rw [h]
      _ = s * z := by group
  have hzx : z * H.C.D.x₃ = H.C.D.x₃ * z :=
    Thompson.commutes_of_mem_WSet H.C.D.c.hp H.C.D.c.hq H.C.D.c.hΩ H.C.D.c.hW _ H.C.hd.hzW _
      H.C.D.x₃_mem
  exact commute_of_index_two (Subgroup.zpowers_le.mpr H.x₃_mem_T) H.T_card hs hsU hzx hzs

theorem s_conj_z_cases {s : G} (hs : s ∈ H.T₃) (hsU : s ∉ Subgroup.zpowers H.C.D.x₃) :
    s * z * s⁻¹ = H.C.D.F.j ∨ s * z * s⁻¹ = H.C.D.F.j * z := by
  have hsW : s * z * s⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (H.hTN hs) z).mp H.C.hd.hzW
  have h2 : s * z * s⁻¹ * (s * z * s⁻¹) = 1 := by
    calc s * z * s⁻¹ * (s * z * s⁻¹) = s * (z * z) * s⁻¹ := by group
      _ = 1 := by rw [H.C.hzK.sq]; group
  rcases T7B.mem_closure_pair H.C.hjJ.sq H.C.hzK.sq H.C.hjJ.ne_one H.C.hzK.ne_one H.C.comm_jz
    (H.C.mem_closure_of_mem_W hsW h2) with h | h | h | h
  · exfalso
    apply H.C.hzK.ne_one
    calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · exact absurd h (H.s_not_comm_z hs hsU)
  · exact Or.inr h

theorem s_mem_normalizer_B {s : G} (hs : s ∈ H.T₃) (hsU : s ∉ Subgroup.zpowers H.C.D.x₃) :
    s ∈ Subgroup.normalizer (H.B : Set G) := by
  have hsj : s * H.C.D.F.j * s⁻¹ = H.C.D.F.j := by
    rw [(e189_commute_of_mem H.C.hjJ (H.hT.1 hs)).symm]; group
  have hsa : s * H.a * s⁻¹ = H.a := by rw [H.comm_T hs]; group
  refine mem_normalizer_closure fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h <;> rw [h]
  · have e : s * (H.C.D.F.j * H.a) * s⁻¹ = (s * H.C.D.F.j * s⁻¹) * (s * H.a * s⁻¹) := by group
    rw [e, hsj, hsa]
    exact H.ja_mem_B
  · rw [hsj]
    exact H.j_mem_B
  · rcases H.s_conj_z_cases hs hsU with h' | h' <;> rw [h']
    · exact H.j_mem_B
    · exact H.B.mul_mem H.j_mem_B H.z_mem_B

theorem closure_jz_le_B : Subgroup.closure ({H.C.D.F.j, z} : Set G) ≤ H.B := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h <;> rw [h]
  exacts [H.j_mem_B, H.z_mem_B]

theorem closure_jz : IsElemAbelian2 (Subgroup.closure ({H.C.D.F.j, z} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair H.C.hjJ.sq H.C.hzK.sq H.C.hjJ.ne_one H.C.hzK.ne_one
    H.C.z_ne_j.symm H.C.comm_jz

theorem centralizer_z_le_gamma2 :
    Subgroup.centralizer ({z} : Set G) ≤ gamma2 H.B (Subgroup.centralizer ({z} : Set G)) := by
  have hst := H.C.hs.stand
  have hΩ := hst.hyp
  have hB := H.B_isElemAbelian
  have hBC : H.B ≤ Subgroup.centralizer ({z} : Set G) := fun _ hb =>
    Lemma52Proof.le_centralizer_of_mem hB H.z_mem_B hb
  have hO := S24.oddCore_le_gamma2_of hB H.B_card hBC
  have hK := S24.le_gamma2_of_trivial hΩ H.z_mem_B H.a_mem_B H.ha2 H.ha1 H.a_ne_z.symm H.comm_z
    hO hst.mem H.C.hzK (H.K_tq H.a H.ha2 H.haR).2
  have hK' := S24.le_gamma2_of_trivial hΩ H.z_mem_B H.a_mem_B H.ha2 H.ha1 H.a_ne_z.symm H.comm_z
    hO H.C.hs.hK'.1 H.C.hzK' (H.K'_tq H.a H.ha2 H.haR').2
  intro c hc
  obtain ⟨q, hq, c₀, hc₀, hcomm, rfl⟩ := T7K.centralizer_eq_sup_mul H.C.hs H.C.j_mem_sup
    H.C.hjJ.ne_one H.C.z_ne_j.symm H.C.hjJ.sq hc
  refine Subgroup.mul_mem _ ((sup_le hK hK') hq) ?_
  have hcz : z * c₀ = c₀ * z := (Subgroup.mem_centralizer_singleton_iff.mp hc₀).symm
  exact T7K.le_gamma2 H.closure_jz_le_B H.closure_jz
    ⟨hc₀, T7B.mem_centralizer_closure_pair hcomm.symm hcz⟩

theorem alphaOf_eq_bot [IsSimpleGroup G] :
    ∀ A : Subgroup G, A ≤ H.B → IsElemAbelian2 A 2 → alphaOf A = ⊥ := by
  obtain ⟨hodd, halpha⟩ := lemma54_odd_and_eq H.hyp51 H.closure_jz_le_B H.closure_jz
  set α₀ := alphaOf (Subgroup.closure ({H.C.D.F.j, z} : Set G)) with hα₀
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (α₀ : Set G) :=
    H.centralizer_z_le_gamma2.trans (gamma2_le_normalizer_alphaOf halpha _)
  obtain ⟨s, hsT, hsU⟩ := H.exists_s
  have hsα : s ∈ Subgroup.normalizer (α₀ : Set G) :=
    normalizer_alpha halpha H.closure_jz_le_B H.closure_jz (H.s_mem_normalizer_B hsT hsU)
  have hrα : H.C.D.F.ρ.r ∈ Subgroup.normalizer (α₀ : Set G) := hCz H.C.r_mem_centralizer_z
  have hj : Subgroup.centralizer ({H.C.D.F.j} : Set G) ≤ Subgroup.normalizer (α₀ : Set G) ∧
      Subgroup.centralizer ({H.C.D.F.j * z} : Set G) ≤ Subgroup.normalizer (α₀ : Set G) := by
    rcases H.s_conj_z_cases hsT hsU with h | h
    · have h1 := T7A.centralizer_conj_le hsα h.symm hCz
      exact ⟨h1, T7A.centralizer_conj_le hrα H.C.r_conj_j.symm h1⟩
    · have h2 := T7A.centralizer_conj_le hsα h.symm hCz
      exact ⟨T7A.centralizer_conj_le hrα H.C.r_conj_jz.symm h2, h2⟩
  have hCu : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (α₀ : Set G) := by
    intro c hc
    rcases H.C.u_cases with h | h
    · exact hj.1 (by rw [← h]; exact hc)
    · exact hj.2 (by rw [← h]; exact hc)
  have hN : Subgroup.normalizer (α₀ : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← S24.sup_centralizer_eq_top_of H.C.hs H.C.hd]
    exact sup_le hCu hCz
  have hα := T7B.eq_bot_of_normalizer_eq_top hodd hN (T7B.two_dvd_natCard H.C.hs.hz)
  intro A hAB hA
  rw [halpha A hAB hA, hα]

end HCtx

end S24B

end CFSG.ClassicalInvolution.Asc77
