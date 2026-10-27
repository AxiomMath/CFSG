module

public import CFSG.LargeExtraspecial.S10EightOC
public import CFSG.LargeExtraspecial.S10EightOB
public import CFSG.LargeExtraspecial.S10FourN

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
open CFSG.RankThree.Literature.FSmith (zmod2_cases)

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem exists_good_of_mem_orbit {K : Subgroup S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG) {σ : S.O}
    (hgood : ∀ m : S.M, S.ρ m ∈ Rbar S g σ → K.map (cK S m) = K) {v : S.Qt}
    (hv : v ∈ orbit S g σ) :
    ∃ m : S.M, S.ρ m ∈ Rbar S g σ ∧ v = S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∧
      K.map (cK S m) = K := by
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  exact ⟨m, hx, ρ_cl_conj_z S m haQ, hgood m hx⟩

theorem ρ_ρ_cl (haQ : g * S.z * g⁻¹ ∈ S.QG) (k m : S.M) :
    ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹)) =
      S.cl (((k * m : S.M) : G) * g * S.z * (((k * m : S.M) : G) * g)⁻¹) := by
  rw [← ρ_cl_conj_z S m haQ, ← ρ_cl_conj_z S (k * m) haQ, map_mul]
  rfl

theorem conj_mem_Lbar_mul_mul (h m : S.M) {x : S.O} (hx : x ∈ S.Lbar ((m : G) * g)) :
    S.ρ h * x * (S.ρ h)⁻¹ ∈ S.Lbar (((h * m : S.M) : G) * g) := by
  have := conj_mem_Lbar_mul S h hx
  rwa [show (h : G) * ((m : G) * g) = ((h * m : S.M) : G) * g by
    rw [Subgroup.coe_mul, mul_assoc]] at this

theorem Dec108.exists_good_space (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g)
    (_hno : ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z → ¬ S.HasTypeAInL g')
    {X : Hyp10 S g t} (h7 : 7 ≤ S.width) {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
    (_h4 : ∀ k₀ k : S.M, ⁅Yb, Yb⁆.map (cK S k₀) = ⁅Yb, Yb⁆ →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((k₀ : G) * g)) →
      ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆) :
    ∃ U : Submodule (ZMod 2) S.Qt, finrank (ZMod 2) U = 3 ∧ ∀ v ∈ U, v ≠ 0 →
      ∃ k : S.M, v = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∧
        ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆ := by
  have haQ := X.haQ
  obtain ⟨F, hFY, -, y, hyY, hyL, hπy⟩ := D.exists_frame hCE
  obtain ⟨k, hkN, hτA, hτt⟩ :=
    (timmesfeld_10_5 hCE X (timmesfeld_10_4_self hCE X h7)).resolve_left (by omega)
  obtain ⟨τ, hτ⟩ : ∃ τ : S.O, τ = S.ρ k * t * (S.ρ k)⁻¹ := ⟨_, rfl⟩
  rw [← hτ] at hτA hτt
  have Y : Hyp10 S g τ := X.conj' hkN hτ
  have hτE : τ ∈ S.Lbar g ⊓ Xb := ⟨hτA.1, D.dec.Nbar_le hCE X hτA.2⟩
  have htE : t ∈ S.Lbar g ⊓ Xb := D.t_mem_Ebar hCE
  have hgoodR : ∀ m : S.M, S.ρ m ∈ Rbar S g t → ⁅Yb, Yb⁆.map (cK S m) = ⁅Yb, Yb⁆ :=
    fun m hm => map_cK_eq_of_conj_mem fun y' hy' => D.dec.conj_mem_commutator hm hy'
  have hkg : ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆ := by
    refine D.map_commutator_eq hCE hP hτE Y.ht1 ?_
    rw [mem_map_cK_iff, hτ]
    have e1 : (S.ρ k)⁻¹ * (S.ρ k * t * (S.ρ k)⁻¹) * S.ρ k = t := by group
    rw [e1]
    exact htE
  obtain ⟨n, hnN, hn⟩ := exists_conj_eq_mul_t hCE X hkN hτ hτA.2 hτt
  obtain ⟨mn, hmn⟩ : ∃ mn : S.M, S.ρ mn = n := MonoidHom.mem_range.mp (Rbar_le_Mbar hnN.1)
  have hmng := hgoodR mn (hmn ▸ hnN.1)
  have hna : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    (mem_Nbar.mp hnN).2 _ (cl_a_mem_Vt X.ht)
  obtain ⟨hq1, hq2, hpf, -, hE0, hEa0⟩ := E10_facts
  obtain ⟨e, hφe⟩ : ∃ e : Vt S g t, F.φ e = E10 := ⟨F.φ.symm E10, F.φ.apply_symm_apply E10⟩
  have he0 : e ≠ 0 := fun h => hE0 (by rw [← hφe, h, map_zero])
  have hea0 : e + aV X.ht ≠ 0 := fun h => hEa0 (by rw [← hφe, ← F.base, ← map_add, h, map_zero])
  have heo : (e : S.Qt) ∈ orbit S g t := (F.mem_orbit_iff he0).mpr (by rw [hφe]; exact hq1)
  have heao : ((e + aV X.ht : Vt S g t) : S.Qt) ∈ orbit S g t :=
    (F.mem_orbit_iff hea0).mpr (by rw [map_add, hφe, F.base]; exact hq2)
  obtain ⟨me, hmeR, hme, hmeg⟩ := exists_good_of_mem_orbit haQ hgoodR heo
  obtain ⟨me', hme'R, hme', hme'g⟩ := exists_good_of_mem_orbit haQ hgoodR heao
  have heP : (e : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) :=
    (beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ e).mp
      (by rw [F.beta_eq, F.base, hφe]; exact hpf)
  obtain ⟨eτ, heτ⟩ : ∃ eτ : S.Qt, eτ = ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e := ⟨_, rfl⟩
  have hfixk := fix_cl_of_mem_normalizer X.H hkN
  have heτ_cl : eτ = S.cl (((k * me : S.M) : G) * g * S.z * (((k * me : S.M) : G) * g)⁻¹) := by
    rw [heτ, hme, ρ_ρ_cl haQ]
  have heτa_cl : eτ + S.cl (g * S.z * g⁻¹) =
      S.cl (((k * me' : S.M) : G) * g * S.z * (((k * me' : S.M) : G) * g)⁻¹) := by
    rw [← ρ_ρ_cl haQ, ← hme', Submodule.coe_add, map_add, ← heτ,
      show ((aV X.ht : Vt S g t) : S.Qt) = S.cl (g * S.z * g⁻¹) from rfl, hfixk]
  have hkmeg := map_cK_mul_eq hkg hmeg
  have hkme'g := map_cK_mul_eq hkg hme'g
  have heτV : eτ ∉ Vt S g t := by
    rw [heτ]
    exact D.conj_not_mem_Vt hCE hP hFY hyY hyL hπy hkN hτ hτA hτt
      (fun γ hγ a b => by rw [hφe]; exact E10_ne_comb γ hγ a b)
  have heτP : eτ ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [heτ]
    exact apply_mem_clSub_Qa_of_normalizer X.H hkN heP
  have heτVτ : eτ ∈ Vt S g τ := by
    rw [heτ, mem_Vt_conj' haQ hτ, inv_apply_apply_O]
    exact e.2
  have hfixτ := (commSpace_t_eq Y.H Y.C Y.ht Y.ht1 Y.hVQ).2
  have hVtWτ : Vt S g t ≤ Wt S g τ := fun v hv => by
    rw [← hfixτ, mem_fixSpace]
    exact (mem_Nbar.mp hτA.2).2 v hv
  have hVτW : Vt S g τ ≤ Wt S g t := Vt_le_Wt_symm hVtWτ
  have htfix : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) eτ = eτ := by
    have hc : eτ ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [(commSpace_t_eq Y.H Y.C Y.ht Y.ht1 Y.hVQ).1]
      exact heτVτ
    obtain ⟨x, rfl⟩ := mem_commSpace.mp hc
    have htx : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t := by
      rw [← (commSpace_t_eq X.H X.C X.ht X.ht1 X.hVQ).1]
      exact sub_mem_commSpace _ x
    have hτfix := (mem_Nbar.mp hτA.2).2 _ htx
    have hcomm : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, Lbar_comm S haQ X.ht Y.ht]
    have key : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) -
        ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) = (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) - ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by
      rw [map_sub, map_sub, ← LinearEquiv.mul_apply, hcomm, LinearEquiv.mul_apply]
      abel
    rw [hτfix, sub_self, sub_eq_zero] at key
    exact key
  obtain ⟨k₀, hk₀, -, hb₀⟩ := X.exists_pair
  obtain ⟨-, -, -, -, hN⟩ := timmesfeld_10_1_two hCE X hk₀ hb₀
  have hc : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) eτ - eτ ∈ Vt S g t := hN n hnN eτ (hVτW heτVτ)
  obtain ⟨w, hwL, hπw, hwv, hwn⟩ := D.exists_ystar hCE hyY hyL hπy hnN heτP heτV htfix
  obtain ⟨hqc, hqca⟩ := Dec108.fix_τ₂_of_sub (X := X) hwL hπw hwv hwn hc
  obtain ⟨c, hcdef⟩ : ∃ c : S.Qt, c = (n : S.Qt ≃ₗ[ZMod 2] S.Qt) eτ - eτ := ⟨_, rfl⟩
  have hneτ : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) eτ = eτ + c := by rw [hcdef]; abel
  have hneτ_cl : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) eτ = S.cl (((mn * (k * me) : S.M) : G) * g *
      S.z * (((mn * (k * me) : S.M) : G) * g)⁻¹) := by
    rw [heτ_cl, ← hmn, ρ_ρ_cl haQ]
  have hneτa_cl : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) eτ + S.cl (g * S.z * g⁻¹) =
      S.cl (((mn * (k * me') : S.M) : G) * g * S.z * (((mn * (k * me') : S.M) : G) * g)⁻¹) := by
    rw [← ρ_ρ_cl haQ, ← heτa_cl, hmn, map_add, hna]
  have hτL : ∀ m : S.M, S.ρ m ∈ Rbar S g t → τ ∈ S.Lbar (((k * m : S.M) : G) * g) := by
    intro m hm
    rw [mem_Lbar_mul_iff, map_mul, hτ]
    have e1 : (S.ρ k * S.ρ m)⁻¹ * (S.ρ k * t * (S.ρ k)⁻¹) * (S.ρ k * S.ρ m) =
        (S.ρ m)⁻¹ * t * S.ρ m := by group
    rw [e1, show (S.ρ m)⁻¹ * t * S.ρ m = t by
      rw [mul_assoc, ← commute_of_mem_Rbar haQ hm, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact X.ht
  have hτtL : τ * t ∈ S.Lbar (((mn * (k * me) : S.M) : G) * g) := by
    rw [← hn, ← hmn]
    exact conj_mem_Lbar_mul_mul mn (k * me) (hτL me hmeR)
  have hmem_t : ∀ m : S.M, τ ∈ S.Lbar ((m : G) * g) → τ * t ∈ S.Lbar ((m : G) * g) →
      S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∈ Vt S g t := by
    intro m h1 h2
    have h3 := mul_mem (inv_mem h1) h2
    rw [← mul_assoc, inv_mul_cancel, one_mul] at h3
    exact cl_mem_Vt h3
  have hQkme := conj_mem_QG' S (k * me).2 haQ
  have hQkme' := conj_mem_QG' S (k * me').2 haQ
  have hQn := conj_mem_QG' S (mn * (k * me)).2 haQ
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) eτ = eτ := by rw [hneτ, h0, add_zero]
    have hL := Lbar_eq_of_cl_eq S hQkme (conj_ne_z' S (k * me).2 X.H.conj_ne) hQn
      (by rw [← hneτ_cl, h1, heτ_cl])
    rw [hL] at hτtL
    exact heτV (heτ_cl ▸ hmem_t _ (hτL me hmeR) hτtL)
  have hca : c ≠ S.cl (g * S.z * g⁻¹) := by
    intro hca
    have h1 : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) eτ = eτ + S.cl (g * S.z * g⁻¹) := by rw [hneτ, hca]
    have hL := Lbar_eq_of_cl_eq S hQkme' (conj_ne_z' S (k * me').2 X.H.conj_ne) hQn
      (by rw [← hneτ_cl, h1, heτa_cl])
    rw [hL] at hτtL
    have h2 := hmem_t _ (hτL me' hme'R) hτtL
    rw [← heτa_cl] at h2
    apply heτV
    have h3 := sub_mem h2 (cl_a_mem_Vt X.ht)
    rwa [add_sub_cancel_right] at h3
  have hcV : c ∈ Vt S g t := hcdef ▸ hc
  have hcv0 : (⟨c, hcV⟩ : Vt S g t) ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  have hcav0 : (⟨c, hcV⟩ + aV X.ht : Vt S g t) ≠ 0 := by
    intro h
    apply hca
    have := congrArg Subtype.val h
    rw [Submodule.coe_add, ZeroMemClass.coe_zero, ← ZModModule.sub_eq_add,
      sub_eq_zero] at this
    exact this
  have hφc : F.φ ⟨c, hcV⟩ = F.φ ⟨_, hc⟩ := by congr 1; exact Subtype.ext hcdef
  have hco : c ∈ orbit S g t := (F.mem_orbit_iff hcv0).mpr (by rw [hφc]; exact hqc)
  have hcao : c + S.cl (g * S.z * g⁻¹) ∈ orbit S g t := by
    have := (F.mem_orbit_iff hcav0).mpr (by rw [map_add, F.base, hφc]; exact hqca)
    rw [Submodule.coe_add] at this
    exact this
  obtain ⟨mc, -, hmc, hmcg⟩ := exists_good_of_mem_orbit haQ hgoodR hco
  obtain ⟨mca, -, hmca, hmcag⟩ := exists_good_of_mem_orbit haQ hgoodR hcao
  have ha0 : S.cl (g * S.z * g⁻¹) ≠ 0 := fun h => aV_ne_zero X.H X.ht (Subtype.ext h)
  have hind : ∀ a b c' : ZMod 2, a • S.cl (g * S.z * g⁻¹) + b • eτ + c' • c = 0 →
      a = 0 ∧ b = 0 ∧ c' = 0 := by
    intro a b c' h
    rcases zmod2_cases b with rfl | rfl
    · rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c' with rfl | rfl
      · exact ⟨rfl, rfl, rfl⟩
      · exact absurd (by simpa using h) hc0
      · exact absurd (by simpa using h) ha0
      · refine absurd ?_ hca
        have h' : S.cl (g * S.z * g⁻¹) + c = 0 := by simpa using h
        rw [← ZModModule.sub_eq_add, sub_eq_zero] at h'
        exact h'.symm
    · exfalso
      apply heτV
      have h' : a • S.cl (g * S.z * g⁻¹) + eτ + c' • c = 0 := by simpa using h
      have h2 : eτ = a • S.cl (g * S.z * g⁻¹) + c' • c := by
        have e3 : eτ = (a • S.cl (g * S.z * g⁻¹) + eτ + c' • c) +
            (a • S.cl (g * S.z * g⁻¹) + c' • c) := by
          rw [show (a • S.cl (g * S.z * g⁻¹) + eτ + c' • c) + (a • S.cl (g * S.z * g⁻¹) + c' • c)
            = eτ + (a • S.cl (g * S.z * g⁻¹) + a • S.cl (g * S.z * g⁻¹)) + (c' • c + c' • c) by
              abel, ZModModule.add_self, ZModModule.add_self, add_zero, add_zero]
        rw [e3, h', zero_add]
      rw [h2]
      exact add_mem (Submodule.smul_mem _ _ (cl_a_mem_Vt X.ht)) (Submodule.smul_mem _ _ hcV)
  refine exists_finrank_three (fun v => ∃ k : S.M,
    v = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∧ ⁅Yb, Yb⁆.map (cK S k) = ⁅Yb, Yb⁆)
    hind fun a b c' hv => ?_
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases c' with rfl | rfl
  · exact absurd (by simp) hv
  · exact ⟨mc, by simpa using hmc, hmcg⟩
  · exact ⟨k * me, by simpa using heτ_cl, hkmeg⟩
  · refine ⟨mn * (k * me), ?_, map_cK_mul_eq hmng hkmeg⟩
    rw [← hneτ_cl, hneτ]
    simp
  · exact ⟨1, by simp, map_cK_one _⟩
  · refine ⟨mca, ?_, hmcag⟩
    rw [← hmca]
    simp only [one_smul, zero_smul, add_zero]
    abel
  · refine ⟨k * me', ?_, hkme'g⟩
    rw [← heτa_cl]
    simp only [one_smul, zero_smul, add_zero]
    abel
  · refine ⟨mn * (k * me'), ?_, map_cK_mul_eq hmng hkme'g⟩
    rw [← hneτa_cl, hneτ]
    simp only [one_smul]
    abel

end CFSG.LargeExtraspecial.S10
