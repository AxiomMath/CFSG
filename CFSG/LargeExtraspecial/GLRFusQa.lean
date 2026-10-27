module

public import CFSG.LargeExtraspecial.GLRFusNorm
public import CFSG.LargeExtraspecial.GLRFusFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace Pair

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}

theorem finrank_kerB (h : Pair S X A B) {b : S.Qt} (hb : b ∈ B) (hb0 : b ≠ 0) :
    S.width - 1 ≤ finrank (ZMod 2) (kerB A b) := by
  obtain ⟨a₀, ha₀, ha₀b⟩ := h.exists_polar_eq_one hb hb0
  have hle : A ≤ kerB A b ⊔ Submodule.span (ZMod 2) ({a₀} : Set S.Qt) := by
    intro a ha
    have e : a = (a - polar S.q a b • a₀) + polar S.q a b • a₀ := by abel
    rw [e]
    exact Submodule.add_mem_sup (Mixed.sub_mem_kerB ha₀ ha₀b ha)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (kerB A b)
    (Submodule.span (ZMod 2) ({a₀} : Set S.Qt))
  have h3 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({a₀} : Set S.Qt)) ≤ 1 := by
    have := finrank_span_le_card (R := ZMod 2) ({a₀} : Set S.Qt)
    simpa using this
  rw [h.finrank_A] at h1
  omega

theorem exists_transvection_move (h : Pair S X A B) {α u a' : S.Qt} (hα : α ∈ A) (hu : u ∈ A)
    (ha' : a' ∈ A) (huα : u ∉ Submodule.span (ZMod 2) ({α} : Set S.Qt))
    (ha'α : a' ∉ Submodule.span (ZMod 2) ({α} : Set S.Qt))
    (hd : a' - u ∉ Submodule.span (ZMod 2) ({α} : Set S.Qt)) :
    ∃ t ∈ X, ∃ c ∈ B, (∀ a ∈ A, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a + polar S.q a c • (a' - u)) ∧
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α ∧ (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u = a' := by
  set Nα := Submodule.span (ZMod 2) ({α} : Set S.Qt)
  set d := a' - u with hd_def
  have hdA : d ∈ A := A.sub_mem ha' hu
  have hU : Submodule.span (ZMod 2) ({α, d} : Set S.Qt) ≤ A := by
    rw [Submodule.span_le]
    rintro v (rfl | rfl)
    exacts [hα, hdA]
  have huU : u ∉ Submodule.span (ZMod 2) ({α, d} : Set S.Qt) := by
    intro hm
    obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp hm
    rcases zmod2_eq_zero_or_one y with rfl | rfl
    · rw [zero_smul, add_zero] at hxy
      exact huα (hxy ▸ Nα.smul_mem _ (Submodule.mem_span_singleton_self α))
    · rw [one_smul, hd_def] at hxy
      apply ha'α
      have e3 : a' = -(x • α) + (u + u) := by
        calc a' = -(x • α) + (u + (x • α + (a' - u))) := by abel
          _ = -(x • α) + (u + u) := by rw [hxy]
      rw [e3, two_vec, add_zero]
      exact Nα.neg_mem (Nα.smul_mem _ (Submodule.mem_span_singleton_self α))
  obtain ⟨c, hcB, hcU, hc1⟩ := h.exists_polar_sep hU hu huU
  have hαc : polar S.q α c = 0 := hcU α (Submodule.subset_span (by simp))
  have hdc : polar S.q d c = 0 := hcU d (Submodule.subset_span (by simp))
  obtain ⟨t, ht, hta⟩ := h.exists_transvection hdA hdc
  refine ⟨t, ht, c, hcB, hta, ?_, ?_⟩
  · rw [hta α hα, hαc, zero_smul, add_zero]
  · rw [hta u hu, hc1, one_smul, hd_def]; abel

theorem A_le_of_mem (h : Pair S X A B) {α u : S.Qt} (hα : α ∈ A) {W : Submodule (ZMod 2) S.Qt}
    (hW : ∀ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α → ∀ v ∈ W,
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W)
    (hαW : α ∈ W) (huW : u ∈ W) (huA : u ∈ A)
    (huα : u ∉ Submodule.span (ZMod 2) ({α} : Set S.Qt)) : A ≤ W := by
  set Nα := Submodule.span (ZMod 2) ({α} : Set S.Qt)
  have hNW : Nα ≤ W := (Submodule.span_singleton_le_iff_mem _ _).mpr hαW
  intro a' ha'
  by_cases ha'α : a' ∈ Nα
  · exact hNW ha'α
  by_cases hd : a' - u ∈ Nα
  · rw [show a' = u + (a' - u) by abel]
    exact W.add_mem huW (hNW hd)
  obtain ⟨t, ht, -, -, -, htα, htu⟩ := h.exists_transvection_move hα huA ha' huα ha'α hd
  rw [← htu]
  exact hW t ht htα u huW

end Pair

namespace Data

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {g : G}

theorem z_mem_inf (hD : Data S X A B g) : S.z ∈ S.QG ⊓ S.Qa g :=
  ⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG rfl hD.conj_mem hD.conj_ne⟩

theorem a_mem_inf (hD : Data S X A B g) : g * S.z * g⁻¹ ∈ S.QG ⊓ S.Qa g :=
  ⟨hD.conj_mem, (S.conjBy g).z_mem_QG⟩

theorem card_inf (hD : Data S X A B g) :
    Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (S.width + 1) := by
  have h1 := S.card_Lbar_mul g
  rw [S.card_L0 hD.conj_mem hD.conj_ne, hD.card_Lbar] at h1
  have h4 := hD.four_le
  have e : 2 ^ (2 * S.width) = 2 ^ (S.width - 1) * 2 ^ (S.width + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e] at h1
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h1

theorem finrank_clSub (hD : Data S X A B g) :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = S.width := by
  have h1 := S.card_clPre (S.clSub (S.QG ⊓ S.Qa g))
  rw [S.clPre_clSub inf_le_left hD.z_mem_inf, hD.card_inf, S.card_submodule] at h1
  have h2 : 2 ^ (S.width + 1) = 2 ^ (finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) + 1) := by
    rw [h1, pow_succ, mul_comm]
  have := Nat.pow_right_injective le_rfl h2
  omega

theorem polar_clSub (hD : Data S X A B g) {u v : S.Qt} (hu : u ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) : polar S.q u v = 0 := by
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hu
  obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hv
  exact (S.polar_cl_eq_zero_iff hxQ hyQ).mpr (S.QG_inf_Qa_comm hD.conj_ne hx hy)

theorem apply_clSub (hD : Data S X A B g) {m : S.M}
    (hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  set a := g * S.z * g⁻¹ with ha_def
  have hma : ∃ m' : S.M, S.ρ m' = S.ρ m ∧ (m' : G) * a * (m' : G)⁻¹ = a := by
    rw [S.ρ_cl m hD.conj_mem] at hm
    rcases (S.cl_eq_cl_iff hD.conj_mem (S.conj_mem_QG m.2 hD.conj_mem)).mp hm.symm with h1 | h1
    · exact ⟨m, rfl, h1⟩
    · obtain ⟨u, huQ, hu⟩ :=
        S.exists_conj_eq_mul_z hD.conj_mem (S.s12_conj_z_ne_one g) hD.conj_ne
      have hu1 : S.ρ ⟨u, S.QG_le_M huQ⟩ = 1 := (S.ρ_eq_one_iff _).mpr huQ
      refine ⟨⟨u, S.QG_le_M huQ⟩⁻¹ * m, ?_, ?_⟩
      · rw [map_mul, map_inv, hu1, inv_one, one_mul]
      · change u⁻¹ * (m : G) * a * (u⁻¹ * (m : G))⁻¹ = a
        calc u⁻¹ * (m : G) * a * (u⁻¹ * (m : G))⁻¹ = u⁻¹ * ((m : G) * a * (m : G)⁻¹) * u := by
              group
          _ = u⁻¹ * (u * a * u⁻¹) * u := by rw [h1, hu]
          _ = a := by group
  obtain ⟨m', hρ, hm'a⟩ := hma
  rw [← hρ]
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.ρ_cl m' hxQ]
  have hm'M : (m' : G) ∈ (S.conjBy g).M := by
    rw [(S.conjBy g).mem_M_iff]
    change (m' : G) * a = a * m'
    calc (m' : G) * a = (m' : G) * a * (m' : G)⁻¹ * m' := by group
      _ = a * m' := by rw [hm'a]
  exact S.cl_mem_clSub ⟨S.conj_mem_QG m'.2 hxQ, (S.conjBy g).conj_mem_QG hm'M hx.2⟩
    (S.conj_mem_QG m'.2 hxQ)

theorem inv_clSub (hD : Data S X A B g) :
    ∀ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) →
      ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g),
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  intro x hx hxα v hv
  obtain ⟨m, rfl⟩ := hD.le_Mbar hx
  exact hD.apply_clSub hxα hv

end Data

namespace Data

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {g : G}

theorem not_mem_B (hD : Data S X A B g) {b : S.Qt} (hbW : b ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hbB : b ∈ B) (hb0 : b ≠ 0) : False := by
  set a := g * S.z * g⁻¹ with ha_def
  set T := S.conjBy g
  obtain ⟨k', hk'Q, hk'b⟩ := hD.conj_B hbB hb0
  set y' := k' * S.z * k'⁻¹ with hy'_def
  obtain ⟨y, hyE, hyQ, hyb⟩ := S.mem_clSub_iff.mp hbW
  have hy'E : y' ∈ S.QG ⊓ S.Qa g := by
    rcases (S.cl_eq_cl_iff hyQ hk'Q).mp (hyb.trans hk'b.symm) with h | h
    · rw [h]; exact hyE
    · rw [h]; exact (S.QG ⊓ S.Qa g).mul_mem hyE hD.z_mem_inf
  have hαA : S.cl a ∈ A := hD.cl_mem
  have hy'a : y' ≠ a := by
    intro h
    apply hb0
    have hb' : b ∈ A ⊓ B := ⟨by rw [← hk'b, h]; exact hαA, hbB⟩
    rwa [hD.pair.inf_eq, Submodule.mem_bot] at hb'
  have hTz : T.z = a := rfl
  have hgt : (k' * g⁻¹) * T.z * (k' * g⁻¹)⁻¹ = y' := by
    rw [hTz, ha_def, hy'_def]; group
  have hy'1 : y' ≠ 1 := S.s12_conj_z_ne_one k'
  have hne : y' * T.z ≠ T.z := by
    intro h
    apply hy'1
    calc y' = y' * T.z * T.z⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel]
  obtain ⟨u, -, hu, -⟩ := (T.lemma_3_8_1 hgt hy'E.2 (hTz ▸ hy'a)).2 (y' * T.z) (by simp)
    T.z (by simp) hne
  have hya : (u * g) * S.z * (u * g)⁻¹ = y' * a := by
    rw [S.s12_mul_conj_z, ← ha_def]
    exact hu
  have hyaQ : (u * g) * S.z * (u * g)⁻¹ ∈ S.QG := by
    rw [hya]; exact S.QG.mul_mem hy'E.1 hD.conj_mem
  have hcl : S.cl ((u * g) * S.z * (u * g)⁻¹) = b + S.cl a := by
    rw [hya, S.cl_mul hy'E.1 hD.conj_mem, hk'b]
  rcases hD.fusion (u * g) hyaQ with h | h
  · rw [hcl] at h
    apply hb0
    have hb' : b ∈ A ⊓ B := ⟨by simpa using A.sub_mem h hαA, hbB⟩
    rwa [hD.pair.inf_eq, Submodule.mem_bot] at hb'
  · rw [hcl] at h
    apply hD.cl_ne_zero
    have hα' : S.cl a ∈ A ⊓ B := ⟨hαA, by simpa using B.sub_mem h hbB⟩
    rwa [hD.pair.inf_eq, Submodule.mem_bot] at hα'

theorem not_graph (hD : Data S X A B g)
    (hA : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), v ∈ A →
      v ∈ Submodule.span (ZMod 2) ({S.cl (g * S.z * g⁻¹)} : Set S.Qt))
    (hB : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), v ∈ B → v = 0) : False := by
  set W := S.clSub (S.QG ⊓ S.Qa g)
  set α := S.cl (g * S.z * g⁻¹) with hα_def
  set Nα := Submodule.span (ZMod 2) ({α} : Set S.Qt)
  have h4 := hD.four_le
  have hαW : α ∈ W := S.cl_mem_clSub hD.a_mem_inf hD.conj_mem
  have hαA : α ∈ A := hD.cl_mem
  have hNW : Nα ≤ W := (Submodule.span_singleton_le_iff_mem _ _).mpr hαW
  obtain ⟨ev, hevW, hevA⟩ : ∃ ev ∈ W, ev ∉ A := by
    by_contra hc
    push Not at hc
    have hle : W ≤ Nα := fun v hv => hA v hv (hc v hv)
    have h1 := Submodule.finrank_mono hle
    have h2 : finrank (ZMod 2) Nα ≤ 1 := by
      have := finrank_span_le_card (R := ZMod 2) ({α} : Set S.Qt)
      simpa using this
    have h3 := hD.finrank_clSub
    change finrank (ZMod 2) W = S.width at h3
    omega
  have hv : ev ∈ A ⊔ B := by rw [hD.pair.sup_eq]; exact Submodule.mem_top
  obtain ⟨a'', ha''A, b'', hb''B, rfl⟩ := Submodule.mem_sup.mp hv
  have hb0 : b'' ≠ 0 := by
    rintro rfl
    exact hevA (by simpa using ha''A)
  have ha''α : a'' ∉ Nα := by
    intro h
    apply hb0
    refine hB b'' ?_ hb''B
    have := W.sub_mem hevW (hNW h)
    simpa using this
  have hαb : polar S.q α b'' = 0 := by
    have h1 := hD.polar_clSub hαW hevW
    rw [polar_add_right, hD.pair.polar_A hαA ha''A, zero_add] at h1
    exact h1
  obtain ⟨u, huK, huU⟩ : ∃ u ∈ kerB A b'',
      u ∉ Submodule.span (ZMod 2) ({α, a''} : Set S.Qt) := by
    by_contra hc
    push Not at hc
    have h1 := Submodule.finrank_mono (show kerB A b'' ≤ Submodule.span (ZMod 2) {α, a''} from hc)
    have h2 := finrank_span_le_two α a''
    have h3 := hD.pair.finrank_kerB hb''B hb0
    omega
  have hU : Submodule.span (ZMod 2) ({α, u} : Set S.Qt) ≤ A := by
    rw [Submodule.span_le]; rintro v (rfl | rfl); exacts [hαA, huK.1]
  have ha''U : a'' ∉ Submodule.span (ZMod 2) ({α, u} : Set S.Qt) := by
    intro hm
    obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp hm
    rcases zmod2_eq_zero_or_one y with rfl | rfl
    · rw [zero_smul, add_zero] at hxy
      exact ha''α (hxy ▸ Nα.smul_mem _ (Submodule.mem_span_singleton_self α))
    · rw [one_smul] at hxy
      apply huU
      rw [show u = a'' - x • α by rw [← hxy]; abel]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  obtain ⟨c, -, hcU, hc1⟩ := hD.pair.exists_polar_sep hU ha''A ha''U
  have hαc : polar S.q α c = 0 := hcU α (Submodule.subset_span (by simp))
  have huc : polar S.q u c = 0 := hcU u (Submodule.subset_span (by simp))
  obtain ⟨t, ht, hta⟩ := hD.pair.exists_transvection huK.1 huc
  have htα : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α := by
    rw [hta α hαA, hαc, zero_smul, add_zero]
  have htb : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) b'' = b'' := by
    refine (hD.pair.apply_eq_self_iff ht hb''B).mpr fun a ha => ?_
    have hub : polar S.q u b'' = 0 := huK.2
    rw [hta a ha, polar_add_left, polar_smul_left, hub, smul_zero, add_zero]
  have hte : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (a'' + b'') - (a'' + b'') = u := by
    rw [map_add, hta a'' ha''A, hc1, one_smul, htb]; abel
  have huW : u ∈ W := by
    rw [← hte]
    exact W.sub_mem (hD.inv_clSub t ht htα _ hevW) hevW
  exact huU (Submodule.span_mono (by simp) (hA u huW huK.1))

theorem clSub_inf_eq (hD : Data S X A B g) : S.clSub (S.QG ⊓ S.Qa g) = A := by
  set W := S.clSub (S.QG ⊓ S.Qa g)
  set α := S.cl (g * S.z * g⁻¹)
  have hαW : α ∈ W := S.cl_mem_clSub hD.a_mem_inf hD.conj_mem
  by_cases hex : ∃ u ∈ W, u ∈ A ∧ u ∉ Submodule.span (ZMod 2) ({α} : Set S.Qt)
  · obtain ⟨u, huW, huA, huα⟩ := hex
    have hle := hD.pair.A_le_of_mem hD.cl_mem (hD.inv_clSub) hαW huW huA huα
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    rw [hD.pair.finrank_A, hD.finrank_clSub]
  · push Not at hex
    exfalso
    by_cases hexB : ∃ b ∈ W, b ∈ B ∧ b ≠ 0
    · obtain ⟨b, hbW, hbB, hb0⟩ := hexB
      exact hD.not_mem_B hbW hbB hb0
    · push Not at hexB
      exact hD.not_graph hex hexB

theorem QG_inf_Qa_eq (hD : Data S X A B g) : S.QG ⊓ S.Qa g = S.clPre A := by
  rw [← hD.clSub_inf_eq, S.clPre_clSub inf_le_left hD.z_mem_inf]

end Data

end CFSG.LargeExtraspecial.GLR
