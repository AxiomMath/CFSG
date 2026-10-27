module

public import CFSG.GH74.QTGen4.U42.Coords
public import CFSG.GH74.QTGen4.U42.MSplit
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin.A5Model CFSG.Quasithin.H13.A5

namespace CoordData

variable {M : Type*} [Group M] (C : CoordData M)

theorem eq_mul_conj (g : M) {v : M} (hv : v ∈ C.V) {u₀ : W5}
    (h : C.ψ ⟨v, hv⟩ = u₀ * pact (C.ρ g) u₀) :
    v = (C.ψ.symm u₀ : M) * (g * (C.ψ.symm u₀ : M) * g⁻¹) := by
  have hmem : g * (C.ψ.symm u₀ : M) * g⁻¹ ∈ C.V := C.hV.conj_mem _ (C.ψ.symm u₀).2 g
  have h2 : C.ψ ⟨g * (C.ψ.symm u₀ : M) * g⁻¹, hmem⟩ = pact (C.ρ g) u₀ := by
    rw [C.conj_ψ, MulEquiv.apply_symm_apply]
  have h3 : C.ψ (C.ψ.symm u₀ * ⟨g * (C.ψ.symm u₀ : M) * g⁻¹, hmem⟩) = C.ψ ⟨v, hv⟩ := by
    rw [map_mul, MulEquiv.apply_symm_apply, h2, h]
  exact (congrArg Subtype.val (C.ψ.injective h3)).symm

theorem sq_eq_one_of_mem {v : M} (hv : v ∈ C.V) : v * v = 1 := by
  have h : (⟨v, hv⟩ : ↥C.V) * ⟨v, hv⟩ = 1 := by
    apply C.ψ.injective
    rw [map_mul, map_one]
    exact W5_mul_self _
  exact congrArg Subtype.val h

theorem exists_K4 (T : Subgroup M) (hVT : C.V ≤ T)
    (hK4 : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → ∃ t ∈ T, C.ρ t = σ) :
    ∃ a b : M, a ∈ T ∧ b ∈ T ∧ C.ρ a = pa ∧ C.ρ b = pb ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a := by
  obtain ⟨hpa2, hpb2, hpab⟩ := K4_facts
  obtain ⟨a₀, ha₀T, ha₀⟩ := hK4 pa (Or.inr (Or.inl rfl))
  have hs : a₀ * a₀ ∈ C.V := C.mem_of_rho_eq_one (by rw [map_mul, ha₀, hpa2])
  have hsfix : pact (C.ρ a₀) (C.ψ ⟨a₀ * a₀, hs⟩) = C.ψ ⟨a₀ * a₀, hs⟩ :=
    (C.pact_fix_iff a₀ ⟨a₀ * a₀, hs⟩).2 (by group)
  rw [ha₀] at hsfix
  obtain ⟨u₀, hu₀⟩ := fix_pa_eq _ hsfix
  rw [← ha₀] at hu₀
  have hs' := C.eq_mul_conj a₀ hs hu₀
  obtain ⟨u, hu⟩ : ∃ u : M, u = (C.ψ.symm u₀ : M) := ⟨_, rfl⟩
  rw [← hu] at hs'
  have huV : u ∈ C.V := hu ▸ (C.ψ.symm u₀).2
  obtain ⟨a, ha_def⟩ : ∃ a : M, a = u * a₀ := ⟨_, rfl⟩
  have haT : a ∈ T := ha_def ▸ T.mul_mem (hVT huV) ha₀T
  have haρ : C.ρ a = pa := by
    rw [ha_def, map_mul, C.rho_eq_one_of_mem huV, one_mul, ha₀]
  have ha2 : a * a = 1 := by
    calc a * a = (u * (a₀ * u * a₀⁻¹)) * (a₀ * a₀) := by rw [ha_def]; group
      _ = (a₀ * a₀) * (a₀ * a₀) := by rw [← hs']
      _ = 1 := C.sq_eq_one_of_mem hs
  obtain ⟨b₀, hb₀T, hb₀⟩ := hK4 pb (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨w, hw_def⟩ : ∃ w : M, w = b₀ * a * b₀⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have hwV : w ∈ C.V := by
    refine C.mem_of_rho_eq_one ?_
    rw [hw_def]
    simp only [map_mul, map_inv]
    rw [hb₀, haρ]
    exact hpab
  have hwa : a * w * a⁻¹ = w := by
    have h1 : (w * a) * (w * a) = 1 := by
      calc (w * a) * (w * a) = b₀ * (a * a) * b₀⁻¹ := by rw [hw_def]; group
        _ = 1 := by rw [ha2]; group
    have h2 : a * w * a⁻¹ = w⁻¹ := by
      calc a * w * a⁻¹ = w⁻¹ * ((w * a) * (w * a)) * (a * a)⁻¹ := by group
        _ = w⁻¹ := by rw [h1, ha2]; group
    rw [h2]
    exact inv_eq_of_mul_eq_one_right (C.sq_eq_one_of_mem hwV)
  have hwfix : pact (C.ρ a) (C.ψ ⟨w, hwV⟩) = C.ψ ⟨w, hwV⟩ := (C.pact_fix_iff a ⟨w, hwV⟩).2 hwa
  rw [haρ] at hwfix
  obtain ⟨y₀, hy₀⟩ := fix_pa_eq _ hwfix
  rw [← haρ] at hy₀
  have hw' := C.eq_mul_conj a hwV hy₀
  obtain ⟨y, hy⟩ : ∃ y : M, y = (C.ψ.symm y₀ : M) := ⟨_, rfl⟩
  rw [← hy] at hw'
  have hyV : y ∈ C.V := hy ▸ (C.ψ.symm y₀).2
  obtain ⟨b₁, hb₁_def⟩ : ∃ b₁ : M, b₁ = y * b₀ := ⟨_, rfl⟩
  have hb₁T : b₁ ∈ T := hb₁_def ▸ T.mul_mem (hVT hyV) hb₀T
  have hb₁ρ : C.ρ b₁ = pb := by
    rw [hb₁_def, map_mul, C.rho_eq_one_of_mem hyV, one_mul, hb₀]
  have hb₁a : b₁ * a = a * b₁ := by
    have hb₀a : b₀ * a = w * a * b₀ := by rw [hw_def]; group
    calc b₁ * a = y * (b₀ * a) := by rw [hb₁_def]; group
      _ = y * (y * (a * y * a⁻¹)) * a * b₀ := by rw [hb₀a, hw']; group
      _ = (y * y) * (a * y * a⁻¹) * a * b₀ := by group
      _ = a * b₁ := by rw [C.sq_eq_one_of_mem hyV, hb₁_def]; group
  obtain ⟨t, ht_def⟩ : ∃ t : M, t = b₁ * b₁ := ⟨_, rfl⟩
  have htV : t ∈ C.V := by
    refine C.mem_of_rho_eq_one ?_
    rw [ht_def, map_mul, hb₁ρ, hpb2]
  have hconj : a * b₁ * a⁻¹ = b₁ := by rw [← hb₁a]; group
  have hta : a * t * a⁻¹ = t := by
    calc a * t * a⁻¹ = (a * b₁ * a⁻¹) * (a * b₁ * a⁻¹) := by rw [ht_def]; group
      _ = t := by rw [hconj, ht_def]
  have htb : b₁ * t * b₁⁻¹ = t := by rw [ht_def]; group
  have htfa : pact pa (C.ψ ⟨t, htV⟩) = C.ψ ⟨t, htV⟩ := by
    rw [← haρ]
    exact (C.pact_fix_iff a ⟨t, htV⟩).2 hta
  have htfb : pact pb (C.ψ ⟨t, htV⟩) = C.ψ ⟨t, htV⟩ := by
    rw [← hb₁ρ]
    exact (C.pact_fix_iff b₁ ⟨t, htV⟩).2 htb
  obtain ⟨x₀, hx₀a, hx₀⟩ := fix_pa_pb_eq _ htfa htfb
  rw [← hb₁ρ] at hx₀
  have ht' := C.eq_mul_conj b₁ htV hx₀
  obtain ⟨x, hx⟩ : ∃ x : M, x = (C.ψ.symm x₀ : M) := ⟨_, rfl⟩
  rw [← hx] at ht'
  have hxV : x ∈ C.V := hx ▸ (C.ψ.symm x₀).2
  have hxa : a * x = x * a := by
    have h1 : a * x * a⁻¹ = x := by
      have e : (⟨x, hxV⟩ : ↥C.V) = C.ψ.symm x₀ := Subtype.ext hx
      have hfix : pact (C.ρ a) (C.ψ ⟨x, hxV⟩) = C.ψ ⟨x, hxV⟩ := by
        rw [e, MulEquiv.apply_symm_apply, haρ]
        exact hx₀a
      exact (C.pact_fix_iff a ⟨x, hxV⟩).1 hfix
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h1]
  obtain ⟨b, hb_def⟩ : ∃ b : M, b = x * b₁ := ⟨_, rfl⟩
  have hbT : b ∈ T := hb_def ▸ T.mul_mem (hVT hxV) hb₁T
  have hbρ : C.ρ b = pb := by
    rw [hb_def, map_mul, C.rho_eq_one_of_mem hxV, one_mul, hb₁ρ]
  have hb2 : b * b = 1 := by
    calc b * b = (x * (b₁ * x * b₁⁻¹)) * (b₁ * b₁) := by rw [hb_def]; group
      _ = t * t := by rw [← ht', ← ht_def]
      _ = 1 := C.sq_eq_one_of_mem htV
  have hab : a * b = b * a := by
    calc a * b = (a * x) * b₁ := by rw [hb_def]; group
      _ = x * (b₁ * a) := by rw [hxa, hb₁a]; group
      _ = b * a := by rw [hb_def]; group
  exact ⟨a, b, haT, hbT, haρ, hbρ, ha2, hb2, hab⟩

end CoordData

def kleinU {G : Type*} [Group G] (a b : G) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) : Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have hba : b * a = a * b := hab.symm
    have e1 : a * (a * b) = b := by rw [← mul_assoc, ha2, one_mul]
    have e2 : (a * b) * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha2, one_mul]
    have e3 : (a * b) * b = a := by rw [mul_assoc, hb2, mul_one]
    have e4 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb2, mul_one]
    have e5 : (a * b) * (a * b) = 1 := by
      rw [mul_assoc, ← mul_assoc b a b, hba, mul_assoc a b b, hb2, mul_one, ha2]
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [ha2, hb2, hba, e1, e2, e3, e4, e5]
  inv_mem' := by
    have hba : b * a = a * b := hab.symm
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · simp
    · rw [ia]; simp
    · rw [ib]; simp
    · rw [mul_inv_rev, ia, ib, hba]; simp

theorem mem_kleinU_iff {G : Type*} [Group G] (a b : G) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) (x : G) :
    x ∈ kleinU a b ha2 hb2 hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b :=
  Iff.rfl

theorem gaschutzSplitU {G : Type*} [Group G] [Finite G]
    {H V T K0 : Subgroup G} (hVH : V ≤ H) (hVT : V ≤ T) (hTH : T ≤ H)
    (hVn : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V)
    (hVp : IsPGroup 2 V) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hT2 : IsPGroup 2 T) (hidx : ¬ 2 ∣ (T.subgroupOf H).index)
    (hK0T : K0 ≤ T) (hK0V : V ⊓ K0 = ⊥)
    (hdec : ∀ t ∈ T, ∃ v ∈ V, ∃ k ∈ K0, v * k = t) :
    ∃ A : Subgroup G, A ≤ H ∧ A ⊓ V = ⊥ ∧ V ⊔ A = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup H := V.subgroupOf H with hN
  have hNn : N.Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
    (by simpa using hVn g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hNc : IsMulCommutative N := ⟨⟨fun a b => by
    have h := hVc _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp b.2)
    exact Subtype.ext (Subtype.ext h)⟩⟩
  have hNp : IsPGroup 2 N := hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  have hTsub : IsPGroup 2 (T.subgroupOf H) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hPc : ((hTsub.toSylow hidx : Sylow 2 H) : Subgroup H) = T.subgroupOf H :=
    IsPGroup.toSylow_coe hTsub hidx
  obtain ⟨A₀, hA₁, hA₂⟩ := (CFSG.Quasithin.gaschutz hNp (hTsub.toSylow hidx)).mpr
    ⟨K0.subgroupOf H, by
      rw [hPc]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hK0T (Subgroup.mem_subgroupOf.mp hx)),
     by
      rw [eq_bot_iff]
      rintro x ⟨hxN, hxK⟩
      have hv : (x : G) ∈ V ⊓ K0 :=
        ⟨Subgroup.mem_subgroupOf.mp hxN, Subgroup.mem_subgroupOf.mp hxK⟩
      rw [hK0V, Subgroup.mem_bot] at hv
      rw [Subgroup.mem_bot]
      exact Subtype.ext hv,
     by
      rw [hPc]
      apply le_antisymm
      · apply sup_le
        · intro x hx
          exact Subgroup.mem_subgroupOf.mpr (hVT (Subgroup.mem_subgroupOf.mp hx))
        · intro x hx
          exact Subgroup.mem_subgroupOf.mpr (hK0T (Subgroup.mem_subgroupOf.mp hx))
      · intro x hx
        obtain ⟨v, hv, k, hk, hvk⟩ := hdec x hx
        have e : (⟨v, hVH hv⟩ : H) * ⟨k, hTH (hK0T hk)⟩ = x := Subtype.ext hvk
        rw [← e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hv))
          (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hk))⟩
  refine ⟨A₀.map H.subtype, Subgroup.map_subtype_le A₀, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, hxV⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxA
    have hkN : k ∈ N := Subgroup.mem_subgroupOf.mpr hxV
    have hk1 : k ∈ N ⊓ A₀ := ⟨hkN, hk⟩
    rw [hA₁, Subgroup.mem_bot] at hk1
    rw [Subgroup.mem_bot, hk1, map_one]
  · apply le_antisymm (sup_le hVH (Subgroup.map_subtype_le A₀))
    intro x hx
    have htop : (⟨x, hx⟩ : H) ∈ N ⊔ A₀ := by
      rw [hA₂]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_left.mp htop
    have e : (n : G) * (k : G) = x := congrArg Subtype.val hnk
    rw [← e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hn))
      (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩))

open Subgroup in
theorem CoordData.exists_complement_plain {M : Type*} [Group M] [Finite M] (C : CoordData M)
    (T : Subgroup M) (hVT : C.V ≤ T) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index)
    (hρT : ∀ t ∈ T, InK4 (C.ρ t)) (hK4 : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → ∃ t ∈ T, C.ρ t = σ) :
    ∃ A : Subgroup M, A ⊓ C.V = ⊥ ∧ C.V ⊔ A = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, haT, hbT, haρ, hbρ, ha2, hb2, hab⟩ := C.exists_K4 T hVT hK4
  have hne : pa ≠ 1 ∧ pb ≠ 1 ∧ pa * pb ≠ 1 := by decide
  have hK0T : kleinU a b ha2 hb2 hab ≤ T := by
    intro x hx
    rcases (mem_kleinU_iff a b ha2 hb2 hab x).mp hx with h | h | h | h <;> rw [h]
    · exact T.one_mem
    · exact haT
    · exact hbT
    · exact T.mul_mem haT hbT
  have hK0V : C.V ⊓ kleinU a b ha2 hb2 hab = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxK⟩
    rw [Subgroup.mem_bot]
    rcases (mem_kleinU_iff a b ha2 hb2 hab x).mp hxK with h | h | h | h
    · exact h
    · exfalso
      have haV : a ∈ C.V := by rw [← h]; exact hxV
      exact hne.1 (by rw [← haρ]; exact C.rho_eq_one_of_mem haV)
    · exfalso
      have hbV : b ∈ C.V := by rw [← h]; exact hxV
      exact hne.2.1 (by rw [← hbρ]; exact C.rho_eq_one_of_mem hbV)
    · exfalso
      have habV : a * b ∈ C.V := by rw [← h]; exact hxV
      exact hne.2.2 (by rw [← haρ, ← hbρ, ← map_mul]; exact C.rho_eq_one_of_mem habV)
  have hdec : ∀ t ∈ T, ∃ v ∈ C.V, ∃ k ∈ kleinU a b ha2 hb2 hab, v * k = t := by
    intro t ht
    rcases InK4_cases _ (hρT t ht) with h | h | h | h
    · exact ⟨t, C.mem_of_rho_eq_one h, 1, (kleinU a b ha2 hb2 hab).one_mem, mul_one t⟩
    · refine ⟨t * a⁻¹, C.mem_of_rho_eq_one ?_, a,
        (mem_kleinU_iff a b ha2 hb2 hab a).mpr (Or.inr (Or.inl rfl)), by group⟩
      rw [map_mul, map_inv, haρ, h, mul_inv_cancel]
    · refine ⟨t * b⁻¹, C.mem_of_rho_eq_one ?_, b,
        (mem_kleinU_iff a b ha2 hb2 hab b).mpr (Or.inr (Or.inr (Or.inl rfl))), by group⟩
      rw [map_mul, map_inv, hbρ, h, mul_inv_cancel]
    · refine ⟨t * (a * b)⁻¹, C.mem_of_rho_eq_one ?_, a * b,
        (mem_kleinU_iff a b ha2 hb2 hab (a * b)).mpr (Or.inr (Or.inr (Or.inr rfl))), by group⟩
      rw [map_mul, map_inv, map_mul, haρ, hbρ, h, mul_inv_cancel]
  have hVn : ∀ h ∈ (⊤ : Subgroup M), ∀ v ∈ C.V, h * v * h⁻¹ ∈ C.V :=
    fun h _ v hv => C.hV.conj_mem v hv h
  have hVc : ∀ x ∈ C.V, ∀ y ∈ C.V, x * y = y * x := by
    intro x hx y hy
    have h : (⟨x, hx⟩ : ↥C.V) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      apply C.ψ.injective
      rw [map_mul, map_mul]
      exact mul_comm _ _
    exact congrArg Subtype.val h
  have hidx : ¬ 2 ∣ (T.subgroupOf ⊤).index := by
    have h : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rw [h]
    exact hTi
  obtain ⟨A, _, hA1, hA2⟩ := gaschutzSplitU (le_top) hVT le_top hVn
    C.isPGroup_V hVc hT hidx hK0T hK0V hdec
  exact ⟨A, hA1, hA2⟩

end CFSG.GH74.QTGen4.U42
