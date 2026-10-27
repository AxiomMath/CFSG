module

public import CFSG.ClassicalInvolution.Q3.TL4AECoverB
public import CFSG.ClassicalInvolution.Q3.TL3T36

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] {P : Set (Subgroup G)} {k : ℕ}

theorem exists_isUniqueInvolution [Finite G] (I : AEIdent P k) (hk : 5 ≤ k) {L : Subgroup G}
    (hL : L ∈ P) (h8 : Nat.card ↥L = 8) {α : Finset (Fin k)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar α h b) :
    ∃ u : G, ∃ hu : IsUniqueInvolution L u, I.φ ⟨u, le_pSpan hL hu.mem⟩ = zBar α h := by
  have hz : zBar α h ∈ (L.subgroupOf (pSpan P)).map I.φ := by
    rw [hlab]
    exact zBar_mem_memBar α h b
  obtain ⟨u, hu, hue⟩ := I.exists_of_mem_map hL hz
  have hne : u ≠ 1 := by
    rintro rfl
    apply zBar_ne_one hk α h
    rw [← hue]
    exact map_one I.φ
  have hsq : u * u = 1 := by
    refine I.injOn hk hL h8 hlab (L.mul_mem hu hu) L.one_mem ?_
    have e : (⟨u * u, le_pSpan hL (L.mul_mem hu hu)⟩ : ↥(pSpan P)) =
        ⟨u, le_pSpan hL hu⟩ * ⟨u, le_pSpan hL hu⟩ := rfl
    rw [e, map_mul, hue, zBar_mul_self]
    exact (map_one I.φ).symm
  refine ⟨u, ⟨hu, hne, hsq, fun y hy hy2 => ?_⟩, hue⟩
  have hmem : I.φ ⟨y, le_pSpan hL hy⟩ ∈ memBar α h b := by
    rw [← hlab]
    exact I.mem_map hL hy
  have hy2' : I.φ ⟨y, le_pSpan hL hy⟩ * I.φ ⟨y, le_pSpan hL hy⟩ = 1 := by
    rw [← map_mul, ← map_one I.φ]
    congr 1
    exact Subtype.ext hy2
  rcases eq_of_mem_memBar_mul_self hk hmem hy2' with h1 | h1
  · left
    exact I.injOn hk hL h8 hlab hy L.one_mem (h1.trans (map_one I.φ).symm)
  · right
    exact I.injOn hk hL h8 hlab hy hu (h1.trans hue.symm)

theorem mem_aeModel (I : AEIdent P k) (x : ↥(pSpan P)) : I.φ x ∈ TL4.aeModel k := by
  show I.φ x ∈ (aeSub k).map (mkQ k)
  rw [← I.range_eq]
  exact ⟨x, rfl⟩

@[expose] noncomputable def permHom (I : AEIdent P k) : ↥(pSpan P) →* alternatingGroup (Fin k) :=
  ((permQ k).comp I.φ).codRestrict (alternatingGroup (Fin k)) fun x =>
    permQ_mem_alt (mem_aeModel I x)

theorem coe_permHom (I : AEIdent P k) (x : ↥(pSpan P)) :
    ((permHom I x : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) = permQ k (I.φ x) := rfl

theorem permHom_surjective (I : AEIdent P k) : Function.Surjective (permHom I) := by
  rintro ⟨σ, hσ⟩
  have hm : mkQ k (ofPerm σ) ∈ I.φ.range := by
    rw [I.range_eq]
    exact mem_aeModel_ofPerm hσ
  obtain ⟨x, hx⟩ := hm
  refine ⟨x, Subtype.ext ?_⟩
  rw [coe_permHom, hx]
  rfl

theorem mem_ker_permHom (I : AEIdent P k) {x : ↥(pSpan P)} :
    x ∈ (permHom I).ker ↔ permQ k (I.φ x) = 1 := by
  rw [MonoidHom.mem_ker, ← coe_permHom]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem exists_vec_of_mem_ker_permHom (I : AEIdent P k) {x : ↥(pSpan P)}
    (hx : x ∈ (permHom I).ker) :
    ∃ v : Fin k → ZMod 2, ∑ i, v i = 0 ∧ I.φ x = mkQ k (ofVec v) := by
  have hr : I.φ x ∈ (aeSub k).map (mkQ k) := I.range_eq ▸ ⟨x, rfl⟩
  obtain ⟨a, ha, hax⟩ := hr
  have hp : a.perm = 1 := by
    have := (mem_ker_permHom I).mp hx
    rwa [← hax] at this
  refine ⟨a.vec, ha.1, ?_⟩
  rw [← hax]
  congr 1
  exact Wr.ext rfl hp

theorem zSpan_le_ker_permHom [Finite G] (I : AEIdent P k) (hk : 5 ≤ k)
    (h8 : ∀ L ∈ P, Nat.card ↥L = 8) : zSpan P ≤ (permHom I).ker := by
  rw [zSpan, Subgroup.closure_le]
  rintro x ⟨L, hL, hxL⟩
  obtain ⟨α, h, b, hlab⟩ := I.label L hL
  obtain ⟨u, hu, hue⟩ := exists_isUniqueInvolution I hk hL (h8 L hL) hlab
  have hxu : x = ⟨u, le_pSpan hL hu.mem⟩ := Subtype.ext (hxL.eq hu)
  rw [SetLike.mem_coe, mem_ker_permHom, hxu, hue]
  exact zOf_perm _

theorem exists_mem_zSpan_of_mem_ker [Finite G] (I : AEIdent P k) (hk : 5 ≤ k)
    (h8 : ∀ L ∈ P, Nat.card ↥L = 8) {x : ↥(pSpan P)} (hx : x ∈ (permHom I).ker) :
    ∃ w ∈ zSpan P, I.φ w = I.φ x := by
  have hH : ∀ (δ : Finset (Fin k)) (hδ : δ.card = 4), zBar δ hδ ∈ (zSpan P).map I.φ := by
    intro δ hδ
    obtain ⟨L, hL, hlab⟩ := I.label_surj δ hδ true
    obtain ⟨u, hu, hue⟩ := exists_isUniqueInvolution I hk hL (h8 L hL) hlab
    exact ⟨⟨u, le_pSpan hL hu.mem⟩, Subgroup.subset_closure ⟨L, hL, hu⟩, hue⟩
  obtain ⟨v, hv, hxv⟩ := exists_vec_of_mem_ker_permHom I hx
  have hmem := mem_of_zBar_mem hk hH hv
  rw [← hxv] at hmem
  obtain ⟨w, hw, hwe⟩ := hmem
  exact ⟨w, hw, hwe⟩

theorem isPGroup_ker_permHom [Finite G] (I : AEIdent P k) (hk : 5 ≤ k)
    (h8 : ∀ L ∈ P, Nat.card ↥L = 8) (hker : IsPGroup 2 ↥I.φ.ker)
    (hW : ∀ a ∈ zSpan P, ∀ b ∈ zSpan P, a * b = b * a ∧ a * a = 1) :
    IsPGroup 2 ↥(permHom I).ker := by
  rintro ⟨y, hy⟩
  obtain ⟨w, hw, hwe⟩ := exists_mem_zSpan_of_mem_ker I hk h8 hy
  have hκ : w⁻¹ * y ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwe, inv_mul_cancel]
  obtain ⟨j, hj⟩ := hker ⟨_, hκ⟩
  have hj' : (w⁻¹ * y) ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hcomm : Commute w (w⁻¹ * y) := Subgroup.mem_center_iff.mp (I.ker_le hκ) w
  have hw2 : w ^ 2 = 1 := by rw [sq]; exact (hW w hw w hw).2
  have e1 : w ^ 2 ^ (j + 1) = 1 := by rw [pow_succ', pow_mul, hw2, one_pow]
  have e2 : (w⁻¹ * y) ^ 2 ^ (j + 1) = 1 := by rw [pow_succ, pow_mul, hj', one_pow]
  have hyw : y = w * (w⁻¹ * y) := by group
  refine ⟨j + 1, Subtype.ext ?_⟩
  show y ^ 2 ^ (j + 1) = 1
  rw [hyw, hcomm.mul_pow, e1, e2, one_mul]

theorem comm_mem_zSpan_of_mem_ker [Finite G] (I : AEIdent P k) (hk : 5 ≤ k)
    (h8 : ∀ L ∈ P, Nat.card ↥L = 8) (hWn : (zSpan P).Normal) {u : ↥(pSpan P)}
    (hu : u ∈ (permHom I).ker) (x : ↥(pSpan P)) : x * u * x⁻¹ * u⁻¹ ∈ zSpan P := by
  obtain ⟨w, hw, hwe⟩ := exists_mem_zSpan_of_mem_ker I hk h8 hu
  have hκ : w⁻¹ * u ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwe, inv_mul_cancel]
  have hc : ∀ g : ↥(pSpan P), g * (w⁻¹ * u) = (w⁻¹ * u) * g := fun g =>
    Subgroup.mem_center_iff.mp (I.ker_le hκ) g
  have e : x * u * x⁻¹ * u⁻¹ = x * w * x⁻¹ * w⁻¹ := by
    have hu' : u = w * (w⁻¹ * u) := by group
    calc x * u * x⁻¹ * u⁻¹ = x * w * ((w⁻¹ * u) * x⁻¹) * u⁻¹ := by group
      _ = x * w * (x⁻¹ * (w⁻¹ * u)) * u⁻¹ := by rw [hc x⁻¹]
      _ = x * w * x⁻¹ * w⁻¹ := by group
  rw [e]
  exact (zSpan P).mul_mem (hWn.conj_mem w hw x) ((zSpan P).inv_mem hw)

theorem le_ker_permHom_of_normal (I : AEIdent P k) (hk : 5 ≤ k) {T : Subgroup ↥(pSpan P)}
    (hT : T.Normal) (hT2 : IsPGroup 2 ↥T) : T ≤ (permHom I).ker := by
  have hs : IsSimpleGroup (alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hk)
  have hTn : (T.map (permHom I)).Normal := hT.map _ (permHom_surjective I)
  rcases hTn.eq_bot_or_eq_top with h1 | h1
  · intro t ht
    have hmem : permHom I t ∈ T.map (permHom I) := ⟨t, ht, rfl⟩
    rw [h1, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    have h2 : IsPGroup 2 ↥(T.map (permHom I)) := hT2.map _
    rw [h1] at h2
    obtain ⟨σ, hσ⟩ : ∃ σ : alternatingGroup (Fin k), orderOf σ = 3 := by
      have h3 : (Equiv.swap (⟨0, by omega⟩ : Fin k) ⟨1, by omega⟩ *
          Equiv.swap (⟨0, by omega⟩ : Fin k) ⟨2, by omega⟩).IsThreeCycle :=
        Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff])
          (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      exact ⟨⟨_, h3.mem_alternatingGroup⟩, by rw [Subgroup.orderOf_mk, h3.orderOf]⟩
    obtain ⟨j, hj⟩ := h2 ⟨σ, Subgroup.mem_top σ⟩
    have hj' : σ ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hdvd := orderOf_dvd_of_pow_eq_one hj'
    rw [hσ] at hdvd
    have h3 : (3 : ℕ) ∣ 2 ^ j := hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega

end CFSG.ClassicalInvolution.Q3.TL4.AECov
