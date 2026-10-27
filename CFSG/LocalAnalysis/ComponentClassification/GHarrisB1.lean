module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSig5

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

theorem SCert.SE.predE_predF_of_predV : ∀ s ∈ SE.Vlist, SE.predE s ∧ SE.predF s := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem piM_injective (hOM : pPrimeCore 2 ↥D.M = ⊥) : Function.Injective D.piM :=
  (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk']; exact hOM)

omit [Finite G] in
theorem conj_mem_of_normal_image_of_OM (hOM : pPrimeCore 2 ↥D.M = ⊥) {K : Subgroup G}
    (hKS : K ≤ (D.S : Subgroup G))
    (hK : ∀ w (hw : w ∈ (D.S : Subgroup G)), w ∈ K → ∀ c : D.Mb,
      ∃ w' : G, ∃ hw' : w' ∈ (D.S : Subgroup G), w' ∈ K ∧ c * D.barS ⟨w, hw⟩ * c⁻¹ =
        D.barS ⟨w', hw'⟩)
    {g u : G} (hg : g ∈ D.M) (hu : u ∈ K) : g⁻¹ * u * g ∈ K := by
  obtain ⟨w', hw', hw'K, heq⟩ := hK u (hKS hu) hu (D.piM ⟨g, hg⟩)⁻¹
  rw [inv_inv, D.piM_conj hg (D.S_le_M (hKS hu))] at heq
  have h := D.piM_injective hOM heq
  have h' : g⁻¹ * u * g = w' := congrArg Subtype.val h
  rw [h']
  exact hw'K


theorem conj_mem_E_of_OM (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥)
    {g u : G} (hg : g ∈ D.M) (hu : u ∈ D.E) : g⁻¹ * u * g ∈ D.E := by
  have hE := D.toMb.E_normal_Y hC D.pPrimeCore_Mb D.z_comm_Mb
  refine D.conj_mem_of_normal_image_of_OM hOM D.E_le_S (fun w hw hwK c => ?_) hg hu
  obtain ⟨e, he, heq⟩ := hE.conj_mem _ ((D.barS_mem_toMb_E_iff hw).mpr hwK) c
  exact ⟨D.toG e, D.toG_mem e, ⟨e, he, rfl⟩, heq.symm⟩

theorem conj_mem_F_of_OM (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥)
    (hB : D.caseB) {g u : G} (hg : g ∈ D.M) (hu : u ∈ D.F) : g⁻¹ * u * g ∈ D.F := by
  have hF := D.toMb.F_normal_of D.pPrimeCore_Mb D.z_comm_Mb
    (D.toMb.prop38B_of hC D.pPrimeCore_Mb D.z_comm_Mb hB).2.2.1
  refine D.conj_mem_of_normal_image_of_OM hOM D.F_le_S (fun w hw hwK c => ?_) hg hu
  obtain ⟨e, he, heq⟩ := hF.conj_mem _ ((D.barS_mem_toMb_F_iff hw).mpr hwK) c
  exact ⟨D.toG e, D.toG_mem e, ⟨e, he, rfl⟩, heq.symm⟩

theorem M_le_normalizer_V_B (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥)
    (hB : D.caseB) : D.M ≤ normalizer (D.V : Set G) := by
  have key : ∀ g ∈ D.M, ∀ v ∈ D.V, g⁻¹ * v * g ∈ D.V := by
    intro g hg v hv
    obtain ⟨s, hs, rfl⟩ := D.exists_Vlist hv
    obtain ⟨hsE, hsF⟩ := SE.predE_predF_of_predV s hs
    have hE := D.conj_mem_E_of_OM hC hOM hg (D.toG_mem_E_iff.mpr hsE)
    have hF := D.conj_mem_F_of_OM hC hOM hB hg (D.toG_mem_F_iff.mpr hsF)
    obtain ⟨u, hu⟩ := D.exists_toG (D.E_le_S hE)
    rw [← hu] at hE hF ⊢
    refine (D.toG_mem_V_iff).mpr (SE.predV_of_E_F u (D.toG_mem_E_iff.mp hE)
      (D.toG_mem_F_iff.mp hF) (D.toG_injective ?_))
    rw [map_mul, hu, map_one, show g⁻¹ * D.toG s * g * (g⁻¹ * D.toG s * g) =
      g⁻¹ * (D.toG s * D.toG s) * g by group, ← map_mul, SE.sq_of_mem_Vlist s hs, map_one]
    group
  intro g hg
  rw [mem_normalizer_iff]
  intro v
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · have h := key g⁻¹ (inv_mem hg) v hv
    rwa [inv_inv] at h
  · have h := key g hg _ hv
    rwa [show g⁻¹ * (g * v * g⁻¹) * g = v by group] at h


theorem centralizer_x_le_M_B (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hB : D.caseB) (hOG : pPrimeCore 2 G = ⊥) : centralizer ({D.x} : Set G) ≤ D.M := by
  obtain ⟨hP, h30, -, -, ⟨gy, -, hgy⟩, -⟩ := D.fusion_B hC hidx hxa hB
  have h6 : D.FusN 6 5 := D.fusN_of_conj_rep (i := 6) (j := 5)
    (by rw [show SE.invRep 5 = SE.gen 6 by decide]; exact hgy)
  have hx2 : D.x * D.x = 1 := by rw [← map_mul, show SE.gen 6 * SE.gen 6 = 1 by decide, map_one]
  have hcz : D.x * D.z = D.z * D.x := by
    rw [← map_mul, ← map_mul, show SE.gen 6 * SE.gen 0 = SE.gen 0 * SE.gen 6 by decide]
  have hct : D.x * D.t = D.t * D.x := by
    rw [← map_mul, ← map_mul, show SE.gen 6 * SE.invRep 1 = SE.invRep 1 * SE.gen 6 by decide]
  refine le_of_zStar D.isSylowOf_X (D.toG_mem _ |> fun h => mem_inf.mpr ⟨h,
    mem_centralizer_singleton_iff.mpr hcz.symm⟩)
    (orderOf_eq_prime (by rw [pow_two, D.z_mul_z]) D.z_ne_one)
    (fun p hp => by
      have h := D.conj_z_S (mem_inf.mp hp).1
      calc D.z * p = p * (p⁻¹ * D.z * p) := by group
        _ = p * D.z := by rw [h])
    (D.isolated_z_B hP h30 h6 (Or.inl rfl) D.isSylowOf_X ?_) inf_le_right ?_
  · intro p hp q hq h hh
    obtain ⟨s, rfl⟩ := D.exists_toG (mem_inf.mp hp).1
    obtain ⟨s', rfl⟩ := D.exists_toG (mem_inf.mp hq).1
    have e : D.toG (s⁻¹ * s'⁻¹ * s * s') = h⁻¹ * D.z * h := by
      rw [hh, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc : (s⁻¹ * s'⁻¹ * s * s') * (s⁻¹ * s'⁻¹ * s * s') = 1 := D.toG_injective (by
      rw [map_one, map_mul, e,
        show h⁻¹ * D.z * h * (h⁻¹ * D.z * h) = h⁻¹ * (D.z * D.z) * h by group, D.z_mul_z]
      group)
    have hXs : ∀ {r : SE}, D.toG r ∈ D.X → r ∈ SE.Xlist := fun {r} hr => by
      have := D.eS_mem_Xlist hr
      rwa [D.eS_toG] at this
    rcases SE.commX s (hXs hp) s' (hXs hq) hc with h1 | h1
    · exfalso
      have : h⁻¹ * D.z * h = 1 := by
        rw [hh, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h1, map_one]
      exact D.z_ne_one (by
        calc D.z = h * (h⁻¹ * D.z * h) * h⁻¹ := by group
          _ = 1 := by rw [this]; group)
    · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h1]
  · rw [← oddCent_zpowers, D.oddCent_eq_bot hC hidx hxa hOG hx2 hcz hct]
    exact bot_le

theorem centralizer_a3a4_le_M_B (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hB : D.caseB) (hOG : pPrimeCore 2 G = ⊥) : centralizer ({D.a3a4} : Set G) ≤ D.M := by
  obtain ⟨hP, h30, -, hsyl, ⟨gy, -, hgy⟩, -⟩ := D.fusion_B hC hidx hxa hB
  have h6 : D.FusN 6 5 := D.fusN_of_conj_rep (i := 6) (j := 5)
    (by rw [show SE.invRep 5 = SE.gen 6 by decide]; exact hgy)
  have hu2 : D.a3a4 * D.a3a4 = 1 := by rw [← map_mul, SE.invRep_mul_self', map_one]
  have hcz : D.a3a4 * D.z = D.z * D.a3a4 := by
    rw [← map_mul, ← map_mul, show SE.invRep 3 * SE.gen 0 = SE.gen 0 * SE.invRep 3 by decide]
  have hct : D.a3a4 * D.t = D.t * D.a3a4 := by rw [← map_mul, ← map_mul, SE.a3a4_comm_t]
  refine le_of_zStar hsyl (mem_inf.mpr ⟨D.toG_mem _, mem_centralizer_singleton_iff.mpr hcz.symm⟩)
    (orderOf_eq_prime (by rw [pow_two, D.z_mul_z]) D.z_ne_one)
    (fun p hp => by
      have h := D.conj_z_S (mem_inf.mp hp).1
      calc D.z * p = p * (p⁻¹ * D.z * p) := by group
        _ = p * D.z := by rw [h])
    (D.isolated_z_B hP h30 h6 (Or.inr rfl) hsyl ?_) inf_le_right ?_
  · intro p hp q hq h hh
    obtain ⟨s, rfl⟩ := D.exists_toG (mem_inf.mp hp).1
    obtain ⟨s', rfl⟩ := D.exists_toG (mem_inf.mp hq).1
    have e : D.toG (s⁻¹ * s'⁻¹ * s * s') = h⁻¹ * D.z * h := by
      rw [hh, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc : (s⁻¹ * s'⁻¹ * s * s') * (s⁻¹ * s'⁻¹ * s * s') = 1 := D.toG_injective (by
      rw [map_one, map_mul, e,
        show h⁻¹ * D.z * h * (h⁻¹ * D.z * h) = h⁻¹ * (D.z * D.z) * h by group, D.z_mul_z]
      group)
    have hTs : ∀ {r : SE}, D.toG r ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a3a4} : Set G) →
        r ∈ SE.Tlist := fun {r} hr => SE.mem_Tlist r (D.toG_injective (by
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.mp (mem_inf.mp hr).2))
    have hnz : ∀ c : SE, ¬ (h⁻¹ * D.z * h = D.toG c ∧ ∃ k : SE, k⁻¹ * c * k = SE.invRep 3) := by
      rintro c ⟨hzc, k, hk⟩
      apply h30
      refine ⟨(h * D.toG k)⁻¹, ?_⟩
      rw [show SE.invRep (Fin.ofNat 9 0) = SE.gen 0 by decide, show Fin.ofNat 9 3 = 3 by decide,
        ← hk, map_mul, map_mul, map_inv, ← hzc]
      group
    rcases SE.commT s (hTs hp) s' (hTs hq) hc with h1 | h1 | h1 | h1
    · exfalso
      have : h⁻¹ * D.z * h = 1 := by rw [← e, h1, map_one]
      exact D.z_ne_one (by
        calc D.z = h * (h⁻¹ * D.z * h) * h⁻¹ := by group
          _ = 1 := by rw [this]; group)
    · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h1]
    · exact absurd ⟨by rw [← e, h1], 1, by group⟩ (hnz (SE.invRep 3))
    · obtain ⟨k, hk⟩ := SE.a3a4z_conj
      exact absurd ⟨by rw [← e, h1], k, hk⟩ (hnz (SE.invRep 3 * SE.gen 0))
  · rw [← oddCent_zpowers, D.oddCent_eq_bot hC hidx hxa hOG hu2 hcz hct]
    exact bot_le

theorem n_mem_normalizer_V_B (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥)
    (hB : D.caseB) (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 3, 3, 5, 6, 3, 5].getD i i))
    (h30 : ¬ D.FusN 3 0) (h6 : D.FusN 6 5) {n : G} (hnt : n⁻¹ * D.t * n = D.z) :
    n ∈ normalizer (D.V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  have hMN := D.M_le_normalizer_V_B hC hOM hB
  set W := D.V.map (MulAut.conj n⁻¹).toMonoidHom with hW
  have hWM : W ≤ D.M := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hvt : v * D.t = D.t * v := D.Q_comm (D.V_le_Q hv) (D.V_le_Q D.t_mem_V)
    change n⁻¹ * v * n⁻¹⁻¹ * D.z = D.z * (n⁻¹ * v * n⁻¹⁻¹)
    rw [← hnt]
    calc n⁻¹ * v * n⁻¹⁻¹ * (n⁻¹ * D.t * n) = n⁻¹ * (v * D.t) * n := by group
      _ = n⁻¹ * (D.t * v) * n := by rw [hvt]
      _ = n⁻¹ * D.t * n * (n⁻¹ * v * n⁻¹⁻¹) := by group
  have hW2 : IsPGroup 2 W := (D.S.isPGroup'.to_le D.V_le_S).map _
  have hSM : IsSylowOf 2 (D.S : Subgroup G) D.M := (isSylowOf_top D.S).of_le D.S_le_M le_top
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_isSylowOf hSM hWM hW2
  set k := m * n⁻¹ with hk
  have hkV : ∀ v ∈ D.V, k * v * k⁻¹ ∈ D.V := by
    intro v hv
    have hS : k * v * k⁻¹ ∈ (D.S : Subgroup G) := by
      have h := hm _ ⟨v, hv, rfl⟩
      rwa [show m * ((MulAut.conj n⁻¹).toMonoidHom v) * m⁻¹ = k * v * k⁻¹ by
        change m * (n⁻¹ * v * n⁻¹⁻¹) * m⁻¹ = _
        rw [hk]
        group] at h
    by_cases hv1 : v = 1
    · rw [hv1, mul_one, mul_inv_cancel]
      exact one_mem _
    obtain ⟨g, hg⟩ := D.conj_z_of_mem_V h10 h20 hv hv1
    refine D.mem_V_of_conj_z_B hP h30 h6 hS ⟨g * k⁻¹, ?_⟩
    rw [← hg]
    group
  have hVle : D.V.map (MulAut.conj k).toMonoidHom ≤ D.V := by
    rintro _ ⟨v, hv, rfl⟩
    exact hkV v hv
  have hVeq : D.V.map (MulAut.conj k).toMonoidHom = D.V :=
    eq_of_le_of_card_ge hVle (by
      rw [card_map_of_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective])
  have hkN : k ∈ normalizer (D.V : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    exact hVeq
  have h := mul_mem (inv_mem hkN) (hMN hmM)
  rwa [show k⁻¹ * m = n by rw [hk]; group] at h

theorem normalizer_V_eq_top_B (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hB : D.caseB) (hOG : pPrimeCore 2 G = ⊥) : normalizer (D.V : Set G) = ⊤ := by
  have hOM := D.oddCore_M_eq_bot hC hidx hxa hOG
  obtain ⟨hP, h30, -, -, ⟨gy, hgyM, hgy⟩, ⟨g₁, hg₁M, hg₁⟩, -, -, n, hna, hnt, -, s₁, hs₁, s₂,
    hs₂, hedge⟩ := D.fusion_B hC hidx hxa hB
  have h6 : D.FusN 6 5 := D.fusN_of_conj_rep (i := 6) (j := 5)
    (by rw [show SE.invRep 5 = SE.gen 6 by decide]; exact hgy)
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  set H := normalizer (D.V : Set G) with hH
  have hMH : D.M ≤ H := D.M_le_normalizer_V_B hC hOM hB
  have hSH : (D.S : Subgroup G) ≤ H := D.S_le_M.trans hMH
  have hnH : n ∈ H := D.n_mem_normalizer_V_B hC hOM hB hP h30 h6 hnt
  have hN : centralizer ({D.x} : Set G) ≤ H :=
    (D.centralizer_x_le_M_B hC hidx hxa hB hOG).trans hMH
  have hK : centralizer ({D.a3a4} : Set G) ≤ H :=
    (D.centralizer_a3a4_le_M_B hC hidx hxa hB hOG).trans hMH
  have hV : ∀ {u : G}, u ∈ D.V → u ≠ 1 → centralizer ({u} : Set G) ≤ H := fun hu hu1 => by
    obtain ⟨k, hk, rfl⟩ := D.exists_normalizer_V_conj h10 h20 hu hu1
    exact centralizer_le_of_conj hk hMH
  refine D.eq_top_of_centralizer_le hSH fun u hu hu2 hu1 =>
    D.centralizer_le_of_reps hSH ?_ hu hu2 hu1
  intro i
  have h0 : ∀ {j : Fin 9}, j = 0 → centralizer ({D.toG (SE.invRep j)} : Set G) ≤ H := by
    rintro j rfl
    rw [D.toG_invRep_zero]
    exact hMH
  fin_cases i
  · exact h0 rfl
  · exact hV D.t_mem_V D.t_ne_one
  · exact hV D.a1l_mem_V fun h => absurd (D.toG_eq_one_iff.mp h) (by decide)
  · exact hK
  · have h := centralizer_le_of_conj (hMH hg₁M) hK
    rwa [← hg₁, show g₁ * (g₁⁻¹ * D.a1a4 * g₁) * g₁⁻¹ = D.a1a4 by group] at h
  · exact hN
  · have h := centralizer_le_of_conj (hMH hgyM) hN
    rwa [← hgy, show gy * (gy⁻¹ * D.y * gy) * gy⁻¹ = D.y by group] at h
  · have h := centralizer_le_of_conj hnH hK
    rwa [← hna, show n * (n⁻¹ * D.a * n) * n⁻¹ = D.a by group] at h
  · rcases hedge with hedge | hedge
    · have hk : s₂ * n⁻¹ * s₁⁻¹ ∈ H :=
        mul_mem (mul_mem (hSH hs₂) (inv_mem hnH)) (inv_mem (hSH hs₁))
      have h := centralizer_le_of_conj hk hN
      have e : s₂ * n⁻¹ * s₁⁻¹ * D.x * (s₂ * n⁻¹ * s₁⁻¹)⁻¹ = D.al := by
        calc s₂ * n⁻¹ * s₁⁻¹ * D.x * (s₂ * n⁻¹ * s₁⁻¹)⁻¹ =
            s₂ * (n⁻¹ * (s₁⁻¹ * D.x * s₁) * n) * s₂⁻¹ := by group
          _ = D.al := by rw [hedge]; group
      rwa [e] at h
    · have hk : s₁ * n * s₂⁻¹ ∈ H :=
        mul_mem (mul_mem (hSH hs₁) hnH) (inv_mem (hSH hs₂))
      have h := centralizer_le_of_conj hk hN
      have e : s₁ * n * s₂⁻¹ * D.x * (s₁ * n * s₂⁻¹)⁻¹ = D.al := by
        calc s₁ * n * s₂⁻¹ * D.x * (s₁ * n * s₂⁻¹)⁻¹ =
            s₁ * n * (s₂⁻¹ * D.x * s₂) * n⁻¹ * s₁⁻¹ := by group
          _ = D.al := by rw [← hedge]; group
      rwa [e] at h

end GHSylow

end CFSG.ComponentClassification.GHarris
