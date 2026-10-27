module

public import CFSG.LargeExtraspecial.GLRFusQa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

theorem card_GL_succ (n : ℕ) :
    Nat.card (GL (Fin (n + 1)) (ZMod 2)) =
      (2 ^ (n + 1) - 1) * 2 ^ n * Nat.card (GL (Fin n) (ZMod 2)) := by
  rw [Matrix.card_GL_field, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_succ]
  simp only [Fin.val_zero, pow_zero, Fin.val_succ]
  rw [mul_assoc]
  congr 1
  have h : ∀ i : Fin n, 2 ^ (n + 1) - 2 ^ ((i : ℕ) + 1) = 2 * (2 ^ n - 2 ^ (i : ℕ)) := by
    intro i
    rw [pow_succ, pow_succ, ← Nat.sub_mul, mul_comm]
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

omit [Finite G] in
theorem le_normalizer_of_conj {H K : Subgroup G} (h : ∀ y ∈ H, ∀ x ∈ K, y * x * y⁻¹ ∈ K) :
    H ≤ normalizer (K : Set G) := by
  intro y hy
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => h y hy x hx, fun hx => ?_⟩
  have := h y⁻¹ (H.inv_mem hy) _ hx
  simpa [mul_assoc] using this

theorem card_comap_ρ {X : Subgroup S.O} (hX : X ≤ S.Mbar) :
    Nat.card (X.comap S.ρ) = Nat.card S.Q * Nat.card X := by
  set f : X.comap S.ρ →* S.O := S.ρ.comp (X.comap S.ρ).subtype
  have hrange : f.range = X := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hX
  have hker : Nat.card f.ker = Nat.card S.Q := by
    have hle : S.ρ.ker ≤ X.comap S.ρ := fun x hx => by
      rw [mem_comap, MonoidHom.mem_ker.mp hx]; exact X.one_mem
    have e : f.ker = S.ρ.ker.subgroupOf (X.comap S.ρ) := by
      ext x
      simp [f, MonoidHom.mem_ker, mem_subgroupOf]
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, S.ker_ρ]
  have h := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange] at h
  exact h.symm

omit [Finite G] in
theorem QG_le_normalizer_clPre (W : Submodule (ZMod 2) S.Qt) :
    S.QG ≤ normalizer (S.clPre W : Set G) :=
  le_normalizer_of_conj fun y hy x hx =>
    ⟨S.conj_mem_QG (S.QG_le_M hy) hx.1, by rw [S.cl_conj_of_mem hy hx.1]; exact hx.2⟩

namespace Data

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {g : G}

theorem Qa_le_normalizer (hD : Data S X A B g) : S.Qa g ≤ normalizer (S.clPre A : Set G) := by
  rw [← hD.QG_inf_Qa_eq]
  refine le_normalizer_of_conj fun y hy x hx => ⟨?_, (S.conjBy g).QG.mul_mem
    ((S.conjBy g).QG.mul_mem hy hx.2) ((S.conjBy g).QG.inv_mem hy)⟩
  have e : y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
  rw [e]
  refine S.QG.mul_mem ?_ hx.1
  rcases (S.conjBy g).commutator_eq_one_or_z hy hx.2 with h | h
  · rw [h]; exact S.QG.one_mem
  · rw [h]; exact hD.conj_mem

theorem mem_normalizer_of_mem (hD : Data S X A B g) {m : S.M} (hm : S.ρ m ∈ X) :
    (m : G) ∈ normalizer (S.clPre A : Set G) := by
  have h : (m : G) ∈ (X.comap S.ρ).map S.M.subtype := ⟨m, hm, rfl⟩
  rw [← hD.normalizer_inf_M] at h
  exact h.1

theorem exists_conj_eq (hD : Data S X A B g) {x : G} (hx : x ∈ S.clPre A) (hx1 : x ≠ 1) :
    ∃ n ∈ normalizer (S.clPre A : Set G), n * S.z * n⁻¹ = x := by
  by_cases hxz : x = S.z
  · exact ⟨1, one_mem _, by rw [hxz]; group⟩
  obtain ⟨u, hu, huz, -⟩ := S.exists_swap rfl hD.conj_mem hD.conj_ne
  have huN : u ∈ normalizer (S.clPre A : Set G) :=
    sup_le (QG_le_normalizer_clPre A) hD.Qa_le_normalizer hu
  have hcl0 : S.cl x ≠ 0 := by
    rw [Ne, S.cl_eq_zero_iff hx.1]
    rintro (h | h)
    exacts [hx1 h, hxz h]
  obtain ⟨p, hpX, hpα⟩ := hD.pair.exists_apply_eq_of_ne_zero hD.cl_mem hx.2 hD.cl_ne_zero hcl0
  obtain ⟨m, rfl⟩ := hD.le_Mbar hpX
  have hmN := hD.mem_normalizer_of_mem hpX
  rw [S.ρ_cl m hD.conj_mem] at hpα
  have hmaQ := S.conj_mem_QG m.2 hD.conj_mem
  rcases (S.cl_eq_cl_iff hx.1 hmaQ).mp hpα.symm with h | h
  · refine ⟨(m : G) * u, mul_mem hmN huN, ?_⟩
    rw [show (m : G) * u * S.z * ((m : G) * u)⁻¹ = (m : G) * (u * S.z * u⁻¹) * (m : G)⁻¹ by
      group, huz, h]
  · have hxzQ : x * S.z ∈ S.QG := S.QG.mul_mem hx.1 S.z_mem_QG
    have hxz1 : x * S.z ≠ 1 := by
      intro e
      apply hxz
      calc x = x * S.z * S.z⁻¹ := by group
        _ = S.z := by rw [e, one_mul, S.z_inv]
    have hxzz : x * S.z ≠ S.z := fun e => hx1 (by simpa using e)
    obtain ⟨w, hwQ, hw⟩ := S.exists_conj_eq_mul_z hxzQ hxz1 hxzz
    refine ⟨w * (m : G) * u, mul_mem (mul_mem (QG_le_normalizer_clPre A hwQ) hmN) huN, ?_⟩
    rw [show w * (m : G) * u * S.z * (w * (m : G) * u)⁻¹ =
        w * ((m : G) * (u * S.z * u⁻¹) * (m : G)⁻¹) * w⁻¹ by group, huz, h, hw, mul_assoc,
      S.z_mul_z, mul_one]

theorem card_normalizer (hD : Data S X A B g) :
    Nat.card (normalizer (S.clPre A : Set G)) =
      2 ^ (S.width + 1) * Nat.card (GL (Fin (S.width + 1)) (ZMod 2)) := by
  set N := normalizer (S.clPre A : Set G)
  let φ : N →* MulAut G := MulAut.conj.comp N.subtype
  let _ : MulAction N G := MulAction.compHom G φ
  have hsmul : ∀ (n : N) (x : G), n • x = (n : G) * x * (n : G)⁻¹ := fun _ _ => rfl
  have horbit : MulAction.orbit N S.z = (S.clPre A : Set G) \ {1} := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      change (n : G) * S.z * (n : G)⁻¹ ∈ (S.clPre A : Set G) \ {1}
      exact ⟨(mem_normalizer_iff.mp n.2 S.z).mp (S.z_mem_clPre A), S.s12_conj_z_ne_one _⟩
    · rintro ⟨hx, hx1⟩
      obtain ⟨n, hn, hnx⟩ := hD.exists_conj_eq hx hx1
      exact ⟨⟨n, hn⟩, hnx⟩
  have hstab : (MulAction.stabilizer N S.z).map N.subtype = N ⊓ S.M := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hn' : (n : G) * S.z * (n : G)⁻¹ = S.z := MulAction.mem_stabilizer_iff.mp hn
      refine ⟨n.2, S.mem_M_iff.mpr ?_⟩
      calc (n : G) * S.z = (n : G) * S.z * (n : G)⁻¹ * n := by group
        _ = S.z * n := by rw [hn']
    · rintro ⟨hyN, hyM⟩
      refine ⟨⟨y, hyN⟩, MulAction.mem_stabilizer_iff.mpr ?_, rfl⟩
      exact S.s12_conj_z_of_mem_M hyM
  have hcardstab : Nat.card (MulAction.stabilizer N S.z) =
      2 ^ (1 + 2 * S.width) * Nat.card (GL (Fin S.width) (ZMod 2)) := by
    rw [← Subgroup.card_map_of_injective N.subtype_injective, hstab, hD.normalizer_inf_M,
      Subgroup.card_map_of_injective S.M.subtype_injective, card_comap_ρ hD.le_Mbar,
      S.card_Q_eq, hD.pair.card]
  have hind : (MulAction.stabilizer N S.z).index = 2 ^ (S.width + 1) - 1 := by
    rw [MulAction.index_stabilizer, horbit,
      Set.ncard_sdiff_singleton_of_mem (S.clPre A).one_mem, ← Nat.card_coe_set_eq]
    change Nat.card (S.clPre A) - 1 = _
    rw [S.card_clPre, S.card_submodule, hD.pair.finrank_A, pow_succ, mul_comm]
  have h := Subgroup.card_mul_index (MulAction.stabilizer N S.z)
  rw [hcardstab, hind] at h
  rw [← h, card_GL_succ]
  have e : 2 ^ (1 + 2 * S.width) = 2 ^ (S.width + 1) * 2 ^ S.width := by
    rw [← pow_add]; congr 1; ring
  rw [e]
  ring

end Data

end CFSG.LargeExtraspecial.GLR
