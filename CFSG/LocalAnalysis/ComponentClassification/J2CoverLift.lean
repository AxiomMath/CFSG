module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBComplementLifting

public section

namespace CFSG.ComponentClassification.J2Cover.Lift

open CFSG.ComponentClassification.CentralCover CFSG.ComponentClassification.J2Cover.Models

theorem exists_normCocycle_section {E Q : Type*} [Group E] [Group Q] {π : E →* Q} {z : E}
    (hπ : IsCentralDoubleExt π z) (S : Subgroup Q) :
    ∃ (u₀ : S → E) (k : NormCocycle S), (∀ s, π (u₀ s) = s) ∧ u₀ 1 = 1 ∧
      ∀ s t, u₀ s * u₀ t = z ^ (k s t).val * u₀ (s * t) := by
  classical
  let u₀ : S → E := fun s => if s = 1 then 1 else Function.surjInv hπ.surjective s
  have hu₀ : ∀ s, π (u₀ s) = s := by
    intro s
    by_cases hs : s = 1
    · rw [hs]
      simp [u₀]
    · simp only [u₀, hs, ↓reduceIte]
      exact Function.surjInv_eq hπ.surjective s
  have hu₀1 : u₀ 1 = 1 := by simp [u₀]
  let k : S → S → ZMod 2 := fun s t => binCoord (u₀ s * u₀ t) (u₀ (s * t))
  have hk : ∀ s t, u₀ s * u₀ t = z ^ (k s t).val * u₀ (s * t) := fun s t =>
    hπ.eq_pow_binCoord_mul (by rw [map_mul, hu₀, hu₀, hu₀, Subgroup.coe_mul])
  refine ⟨u₀, ⟨k, fun b => ?_, fun a => ?_, fun a b c => ?_⟩, hu₀, hu₀1, hk⟩
  · exact hπ.binCoord_eq (by rw [hu₀1, one_mul, one_mul, ZMod.val_zero, pow_zero, one_mul])
  · exact hπ.binCoord_eq (by rw [hu₀1, mul_one, mul_one, ZMod.val_zero, pow_zero, one_mul])
  · apply hπ.pow_val_mul_cancel (x := u₀ (a * b * c))
    calc z ^ (k a b + k (a * b) c).val * u₀ (a * b * c)
        = z ^ (k a b).val * (z ^ (k (a * b) c).val * u₀ (a * b * c)) := by
          rw [hπ.pow_val_add, mul_assoc]
      _ = u₀ a * u₀ b * u₀ c := by rw [← hk (a * b) c, ← mul_assoc, ← hk a b]
      _ = u₀ a * (z ^ (k b c).val * u₀ (b * c)) := by rw [mul_assoc, hk b c]
      _ = z ^ (k b c).val * (z ^ (k a (b * c)).val * u₀ (a * (b * c))) := by
          rw [hπ.mul_pow_val_mul, hk a (b * c)]
      _ = z ^ (k b c + k a (b * c)).val * u₀ (a * b * c) := by
          rw [hπ.pow_val_add, mul_assoc, mul_assoc a b c]

theorem transfer₂_sum_hN (ε : Fin 6 → ZMod 2) (g h : Models.P) :
    isRightTransversal.transfer₂ (fun s t => ∑ j : Fin 6, ε j * hN j s t) g h =
      ∑ j : Fin 6, ε j * isRightTransversal.transfer₂ (hN j) g h := by
  simp only [IsRightTransversal.transfer₂_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem sum_mul_eFlag (ε : Fin 6 → ZMod 2) : ∑ j : Fin 6, ε j * eFlag j = ε 0 := by
  have h : ∀ j : Fin 6, eFlag j = if j = 0 then 1 else 0 := by decide
  simp [h]

theorem exists_eq_smul_fN_add_coboundary {E : Type*} [Group E] {π : E →* Models.P} {z : E}
    (hπ : IsCentralDoubleExt π z) (u₀ : Sp → E) (hu₀ : ∀ s, π (u₀ s) = s) (hu₀1 : u₀ 1 = 1)
    (k : NormCocycle Sp) (hk : ∀ s t, u₀ s * u₀ t = z ^ (k s t).val * u₀ (s * t)) :
    ∃ (e : ZMod 2) (β : Sp → ZMod 2), ∀ s t, k s t = e * fN s t + coboundary β s t := by
  have hodd : Odd (Fintype.card (Fin 4725)) := by
    rw [Fintype.card_fin]
    decide
  obtain ⟨C, -, hC⟩ :=
    isRightTransversal.exists_coboundary_eq_transfer hπ hodd u₀ hu₀ hu₀1 (fun s t => k s t) hk
  obtain ⟨b, ε, hb⟩ := exists_eq_coboundary_add_sum k
  have hfun : (fun s t => k s t) =
      fun s t => (∑ j : Fin 6, ε j * hN j s t) + coboundary b s t := by
    funext s t
    rw [hb, add_comm]
  have htr : ∀ g h : Models.P, isRightTransversal.transfer₂ (fun s t => k s t) g h =
      (∑ j : Fin 6, ε j * isRightTransversal.transfer₂ (hN j) g h) +
        coboundary (isRightTransversal.transfer₁ b) g h := by
    intro g h
    rw [hfun, isRightTransversal.transfer₂_add_coboundary, transfer₂_sum_hN]
  refine ⟨ε 0, fun s => (∑ j : Fin 6, ε j * bN j s) + isRightTransversal.transfer₁ b s + C s,
    fun s t => ?_⟩
  have h1 : k s t = isRightTransversal.transfer₂ (fun s t => k s t) s t + coboundary C s t :=
    hC s t
  have h2 : ∀ j : Fin 6, isRightTransversal.transfer₂ (hN j) s t =
      eFlag j * fN s t + coboundary (bN j) s t := fun j => transfer₂_hN j.isLt s t
  rw [htr] at h1
  simp only [h2] at h1
  rw [h1]
  simp only [coboundary_apply, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul,
    sum_mul_eFlag, Subgroup.coe_mul]
  ring

theorem not_isComplement'_of_perfect {G : Type*} [Group G] (hG : commutator G = ⊤) {t : G}
    (ht : orderOf t = 2) (B : Subgroup G) (hB : Subgroup.IsComplement' (Subgroup.zpowers t) B) :
    False := by
  have hidx : B.index = 2 := by rw [hB.index_eq_card, Nat.card_zpowers, ht]
  have hcomm : commutator G ≤ B := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      inv_mem_iff, inv_mem_iff]
    tauto
  rw [hG, top_le_iff] at hcomm
  have htB : t ∈ B := hcomm ▸ Subgroup.mem_top t
  have h1 : t = 1 := Subgroup.disjoint_def.1 hB.disjoint (Subgroup.mem_zpowers t) htB
  rw [h1, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem false_of_coboundary {E : Type*} [Group E] [Finite E] (hE : commutator E = ⊤)
    {π : E →* Models.P} {z : E} (hπ : IsCentralDoubleExt π z) (u₀ : Sp → E)
    (hu₀ : ∀ s, π (u₀ s) = s) (β : Sp → ZMod 2)
    (hk : ∀ s t, u₀ s * u₀ t = z ^ (coboundary β s t).val * u₀ (s * t)) : False := by
  have hβ : ∀ s t : Sp, β (s * t) = β s + β t + coboundary β s t := by
    intro s t
    rw [coboundary_apply]
    generalize β s = a
    generalize β t = c
    generalize β (s * t) = d
    revert a c d
    decide
  let σ : Sp →* E := MonoidHom.mk' (fun s => z ^ (β s).val * u₀ s) fun s t => by
    change z ^ (β (s * t)).val * u₀ (s * t) = z ^ (β s).val * u₀ s * (z ^ (β t).val * u₀ t)
    rw [mul_assoc, hπ.mul_pow_val_mul, hk, hβ, hπ.pow_val_add, hπ.pow_val_add]
    simp only [mul_assoc]
  have hπσ : ∀ s, π (σ s) = s := fun s => by
    change π (z ^ (β s).val * u₀ s) = s
    rw [map_mul, hπ.map_pow_val, one_mul, hu₀]
  set K : Subgroup E := σ.range
  have hNK : Subgroup.zpowers z ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxN, s, rfl⟩
    have h1 : π (σ s) = 1 := by
      rw [← MonoidHom.mem_ker, hπ.ker_eq]
      exact hxN
    have hs : s = 1 := Subtype.ext ((hπσ s).symm.trans h1)
    rw [Subgroup.mem_bot, hs, map_one]
  have hsup : Subgroup.zpowers z ⊔ K = Sp.comap π := by
    apply le_antisymm
    · refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
      · rw [Subgroup.mem_comap, hπ.map_z]
        exact Sp.one_mem
      · rintro _ ⟨s, rfl⟩
        rw [Subgroup.mem_comap, hπσ]
        exact s.2
    · intro x hx
      set y : E := σ ⟨π x, hx⟩ with hy
      have hmem : x * y⁻¹ ∈ Subgroup.zpowers z := by
        rw [← hπ.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hy, hπσ]
        exact mul_inv_cancel (π x)
      have hyK : y ∈ K := ⟨⟨π x, hx⟩, rfl⟩
      have hx' : x = x * y⁻¹ * y := by group
      rw [hx']
      exact mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hyK)
  have hidx : (Sp.comap π).index = 4725 := by
    rw [Subgroup.index_comap_of_surjective _ hπ.surjective]
    exact relIndex_S_P
  have hcop : Nat.Coprime (Sp.comap π).index (Nat.card (Subgroup.zpowers z)) := by
    rw [hidx, Nat.card_zpowers, hπ.orderOf_eq]
    norm_num
  have : (Subgroup.zpowers z).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hπ.mem_center)
  obtain ⟨B, -, -, hB⟩ := abelian_normal_coprime_index_complement_lifting hcop hNK hsup
  exact not_isComplement'_of_perfect hE hπ.orderOf_eq B hB

theorem exists_mulEquiv_RfN {E : Type*} [Group E] [Finite E] (hE : commutator E = ⊤)
    {π : E →* Models.P} {z : E} (hπ : IsCentralDoubleExt π z) :
    ∃ ι : Sp.comap π ≃* RfN, (∀ x, ((ι x).snd : Models.P) = π x) ∧
      ((ι.symm ⟨1, 1⟩ : Sp.comap π) : E) = z := by
  obtain ⟨u₀, k, hu₀, hu₀1, hk⟩ := exists_normCocycle_section hπ Sp
  obtain ⟨e, β, hkβ⟩ := exists_eq_smul_fN_add_coboundary hπ u₀ hu₀ hu₀1 k hk
  rcases zmod_two_cases e with rfl | rfl
  · exact (false_of_coboundary hE hπ u₀ hu₀ β fun s t => by
      rw [hk, hkβ, zero_mul, zero_add]).elim
  · obtain ⟨ι, hι, -⟩ := hπ.exists_comap_mulEquiv_of_section Sp u₀ hu₀ fN β fun s t => by
      rw [hk, hkβ, one_mul]
    refine ⟨ι, hι, ?_⟩
    have hzS : z ∈ Sp.comap π := by
      rw [Subgroup.mem_comap, hπ.map_z]
      exact Sp.one_mem
    have h1 : ι ⟨z, hzS⟩ = ⟨1, 1⟩ := by
      refine CocycleExtension.mulEquiv_eq_mk_one_one ι ?_ (Subtype.ext ?_)
      · intro h
        exact hπ.ne_one (congrArg Subtype.val h)
      · rw [hι]
        exact hπ.map_z
    rw [← h1, MulEquiv.symm_apply_apply]

theorem sq_eq_pow_fN {E : Type*} [Group E] {π : E →* Models.P} {z : E}
    (ι : Sp.comap π ≃* RfN) (hι : ∀ x, ((ι x).snd : Models.P) = π x)
    (hιz : ((ι.symm ⟨1, 1⟩ : Sp.comap π) : E) = z) {v : E} {s : Sp} (hv : π v = s)
    (hs : s * s = 1) : v ^ 2 = z ^ (fN s s).val := by
  have hvS : v ∈ Sp.comap π := by
    rw [Subgroup.mem_comap, hv]
    exact s.2
  have hx : (ι ⟨v, hvS⟩).snd = s := Subtype.ext (by rw [hι]; exact hv)
  have hsq : ι (⟨v, hvS⟩ ^ 2) = (⟨1, 1⟩ : RfN) ^ (fN s s).val := by
    rw [CocycleExtension.mk_one_pow_val, map_pow, sq]
    refine CocycleExtension.ext ?_ ?_
    · rw [CocycleExtension.mul_fst, hx, CentralCover.zmod_two_add_self, zero_add]
    · rw [CocycleExtension.mul_snd, hx, hs]
  have h := congrArg (fun y : RfN => ((ι.symm y : Sp.comap π) : E)) hsq
  simp only [MulEquiv.symm_apply_apply, map_pow, SubgroupClass.coe_pow] at h
  rw [hιz] at h
  exact h

theorem fN_elt_four : fN (eS.symm (elt 4)) (eS.symm (elt 4)) = 0 := by
  rw [fN_apply, MulEquiv.apply_symm_apply]
  exact fCoc_elt_four

theorem fCoc_elt_two : fCoc (elt 2) (elt 2) = 1 := by
  rcases fCoc_diag (elt 2) orderOf_elt_two with ⟨h, -⟩ | ⟨-, h⟩
  · rw [fixCount_elt_two] at h
    exact absurd h (by norm_num)
  · exact h

theorem fN_elt_two : fN (eS.symm (elt 2)) (eS.symm (elt 2)) = 1 := by
  rw [fN_apply, MulEquiv.apply_symm_apply]
  exact fCoc_elt_two

theorem elt_two_mul_self : elt 2 * elt 2 = 1 := by
  have h := pow_orderOf_eq_one (elt 2)
  rwa [orderOf_elt_two, sq] at h

theorem eS_symm_mul_self {a : ℕ} (h : elt a * elt a = 1) :
    eS.symm (elt a) * eS.symm (elt a) = 1 := by
  rw [← map_mul, h, map_one]

theorem lift_sq {E : Type*} [Group E] {π : E →* Models.P} {z : E} (hπ : IsCentralDoubleExt π z)
    (ι : Sp.comap π ≃* RfN) (hι : ∀ x, ((ι x).snd : Models.P) = π x)
    (hιz : ((ι.symm ⟨1, 1⟩ : Sp.comap π) : E) = z) {q : Models.P} (hq : orderOf q = 2) {v : E}
    (hv : π v = q) :
    (fixCount (q : Perm315) = 11 ∧ v ^ 2 = 1) ∨ (fixCount (q : Perm315) = 15 ∧ v ^ 2 = z) := by
  obtain ⟨g, hg⟩ := involution_conj_rep q hq
  obtain ⟨l, rfl⟩ := hπ.surjective g
  have key : ∀ {a : ℕ}, elt a * elt a = 1 → π l * q * (π l)⁻¹ = incl (elt a) →
      (l * v * l⁻¹) ^ 2 = z ^ (fN (eS.symm (elt a)) (eS.symm (elt a))).val := by
    intro a ha hla
    refine sq_eq_pow_fN ι hι hιz ?_ (eS_symm_mul_self ha)
    rw [map_mul, map_mul, map_inv, hv, hla, coe_eS_symm]
  have hconj : ∀ w : E, (l * v * l⁻¹) ^ 2 = w → w ∈ Subgroup.center E → v ^ 2 = w := by
    intro w h hw
    rw [conj_pow] at h
    have h' : v ^ 2 = l⁻¹ * w * l := by
      rw [← h]
      group
    rw [h', Subgroup.mem_center_iff.1 hw l⁻¹, inv_mul_cancel_right]
  rcases hg with ⟨h11, hg⟩ | ⟨h15, hg⟩
  · left
    refine ⟨h11, hconj 1 ?_ (Subgroup.one_mem _)⟩
    rw [key elt_four_mul_self hg, fN_elt_four, ZMod.val_zero, pow_zero]
  · right
    refine ⟨h15, hconj z ?_ hπ.mem_center⟩
    rw [key elt_two_mul_self hg, fN_elt_two, zmod_two_val_one, pow_one]

theorem orderOf_eq_four_of_sq {G : Type*} [Group G] {t w : G} (ht : orderOf t = 2)
    (hw : w ^ 2 = t) : orderOf w = 4 := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := w) (by rw [pow_one, hw]; exact ht1)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hw, ← ht, pow_orderOf_eq_one])
  rw [h]
  norm_num

theorem native_sylow_map_and_lift_orders {E : Type*} [Group E] [Finite E]
    (hE : commutator E = ⊤) {π : E →* Models.P} {z : E} (hπ : IsCentralDoubleExt π z) :
    (∃ ι : Sp.comap π ≃* RfN, (∀ x, ((ι x).snd : Models.P) = π x) ∧
      ((ι.symm ⟨1, 1⟩ : Sp.comap π) : E) = z) ∧
    (∀ v : E, orderOf (π v) = 2 → fixCount (π v : Perm315) = 11 → orderOf v = 2) ∧
    (∀ v : E, orderOf (π v) = 2 → fixCount (π v : Perm315) = 15 → v ^ 2 = z ∧ orderOf v = 4) := by
  obtain ⟨ι, hι, hιz⟩ := exists_mulEquiv_RfN hE hπ
  have hne : ∀ v : E, orderOf (π v) = 2 → v ≠ 1 := by
    rintro v hv rfl
    rw [map_one, orderOf_one] at hv
    exact absurd hv (by norm_num)
  refine ⟨⟨ι, hι, hιz⟩, fun v hv h11 => ?_, fun v hv h15 => ?_⟩
  · rcases lift_sq hπ ι hι hιz hv rfl with ⟨-, h⟩ | ⟨h, -⟩
    · exact orderOf_eq_prime h (hne v hv)
    · rw [h11] at h
      exact absurd h (by norm_num)
  · rcases lift_sq hπ ι hι hιz hv rfl with ⟨h, -⟩ | ⟨-, h⟩
    · rw [h15] at h
      exact absurd h (by norm_num)
    · exact ⟨h, orderOf_eq_four_of_sq hπ.orderOf_eq h⟩

@[expose] def fixedCount (q : J2Cover.P) : ℕ := Models.fixCount (q : Equiv.Perm (Fin 315))

theorem fixedCount_eq_fixCount (q : J2Cover.P) :
    fixedCount q = Models.fixCount (q : Equiv.Perm (Fin 315)) :=
  rfl

theorem fixedCount_eq_card (q : J2Cover.P) :
    fixedCount q = Nat.card {i : Fin 315 // (q : Equiv.Perm (Fin 315)) i = i} := by
  rw [fixedCount_eq_fixCount, Models.fixCount, Nat.card_eq_fintype_card]

theorem fixedCount_eq_card_filter (q : J2Cover.P) :
    fixedCount q =
      (Finset.univ.filter fun i : Fin 315 => (q : Equiv.Perm (Fin 315)) i = i).card := by
  rw [fixedCount_eq_fixCount, Models.fixCount, Fintype.card_subtype]

@[expose] noncomputable def toModels : J2Cover.P ≃* Models.P :=
  MulEquiv.subgroupCongr P_eq_autP.symm

theorem coe_toModels (q : J2Cover.P) :
    ((toModels q : Models.P) : Equiv.Perm (Fin 315)) = q :=
  MulEquiv.subgroupCongr_apply _ q

theorem fixCount_toModels (q : J2Cover.P) :
    Models.fixCount ((toModels q : Models.P) : Equiv.Perm (Fin 315)) = fixedCount q := by
  rw [coe_toModels, fixedCount_eq_fixCount]

theorem isCentralDoubleExt {L : Type*} [Group L] {t : L} (ht : orderOf t = 2)
    (hZ : Subgroup.center L = Subgroup.zpowers t) {Q : Type*} [Group Q] (π : L →* Q)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers t) :
    IsCentralDoubleExt π t :=
  ⟨hπ, hZ ▸ Subgroup.mem_zpowers t, ht, hker⟩

end CFSG.ComponentClassification.J2Cover.Lift

namespace CFSG.ComponentClassification.J2Cover

open CFSG.ComponentClassification.CentralCover CFSG.ComponentClassification.J2Cover.Models
open Lift (toModels coe_toModels fixCount_toModels)

theorem ctss_j2_actual_double_cover_native_sylow_map_and_lift_orders
    {L : Type*} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : Subgroup.center L = Subgroup.zpowers t)
    (π : L →* CFSG.ComponentClassification.J2Cover.P) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers t) :
    (∃ ι : Sp.comap (toModels.toMonoidHom.comp π) ≃* RfN,
      (∀ x, (((ι x).snd : Models.P) : Equiv.Perm (Fin 315)) = π x) ∧
      ((ι.symm ⟨1, 1⟩ : Sp.comap (toModels.toMonoidHom.comp π)) : L) = t) ∧
    (∀ q : CFSG.ComponentClassification.J2Cover.P, orderOf q = 2 →
        Lift.fixedCount q = 11 ∨ Lift.fixedCount q = 15) ∧
    (∀ v : L, orderOf (π v) = 2 → Lift.fixedCount (π v) = 11 → orderOf v = 2) ∧
    (∀ v : L, orderOf (π v) = 2 → Lift.fixedCount (π v) = 15 → v ^ 2 = t ∧ orderOf v = 4) := by
  have hπ' : IsCentralDoubleExt (toModels.toMonoidHom.comp π) t :=
    Lift.isCentralDoubleExt ht hZ _ (toModels.surjective.comp hπ) (by
      rw [← hker]
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff])
  obtain ⟨⟨ι, hι, hιz⟩, h11, h15⟩ := Lift.native_sylow_map_and_lift_orders hLq.1 hπ'
  have hord : ∀ v : L, orderOf (toModels.toMonoidHom.comp π v) = orderOf (π v) := fun v =>
    MulEquiv.orderOf_eq toModels (π v)
  refine ⟨⟨ι, fun x => ?_, hιz⟩, fun q hq => ?_,
    fun v hv h => h11 v (by rw [hord]; exact hv) ((fixCount_toModels (π v)).trans h),
    fun v hv h => h15 v (by rw [hord]; exact hv) ((fixCount_toModels (π v)).trans h)⟩
  · rw [hι x]
    exact coe_toModels (π x)
  · rw [← fixCount_toModels]
    exact involution_fixCount (toModels q) (by rw [MulEquiv.orderOf_eq]; exact hq)

end CFSG.ComponentClassification.J2Cover

namespace CFSG.ComponentClassification.J2Cover.Lift

theorem _root_.CFSG.ComponentClassification.J2Cover.j2_double_cover_involution_lift_orders
    {L : Type*} [Group L] [Finite L]
    (hLq : CFSG.Assembly.IsQuasisimple L) {t : L} (ht : orderOf t = 2)
    (hZ : Subgroup.center L = Subgroup.zpowers t)
    (π : L →* CFSG.ComponentClassification.J2Cover.P) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers t) :
    (∀ q : CFSG.ComponentClassification.J2Cover.P, orderOf q = 2 →
        fixedCount q = 11 ∨ fixedCount q = 15) ∧
    (∀ v : L, orderOf (π v) = 2 → fixedCount (π v) = 11 → orderOf v = 2) ∧
    (∀ v : L, orderOf (π v) = 2 → fixedCount (π v) = 15 → v ^ 2 = t ∧ orderOf v = 4) :=
  (ctss_j2_actual_double_cover_native_sylow_map_and_lift_orders hLq ht hZ π hπ hker).2

end CFSG.ComponentClassification.J2Cover.Lift

namespace CFSG.ComponentClassification.J2Cover

theorem j2_double_cover_involution_lift_orders_fixCount
    {L : Type*} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L) {t : L}
    (ht : orderOf t = 2) (hZ : Subgroup.center L = Subgroup.zpowers t)
    (π : L →* CFSG.ComponentClassification.J2Cover.P) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers t) :
    (∀ q : CFSG.ComponentClassification.J2Cover.P, orderOf q = 2 →
        Models.fixCount (q : Equiv.Perm (Fin 315)) = 11 ∨
          Models.fixCount (q : Equiv.Perm (Fin 315)) = 15) ∧
    (∀ v : L, orderOf (π v) = 2 →
      Models.fixCount ((π v : CFSG.ComponentClassification.J2Cover.P) : Equiv.Perm (Fin 315)) =
        11 → orderOf v = 2) ∧
    (∀ v : L, orderOf (π v) = 2 →
      Models.fixCount ((π v : CFSG.ComponentClassification.J2Cover.P) : Equiv.Perm (Fin 315)) =
        15 → v ^ 2 = t ∧ orderOf v = 4) :=
  j2_double_cover_involution_lift_orders hLq ht hZ π hπ hker

end CFSG.ComponentClassification.J2Cover

namespace CFSG.ComponentClassification.J2Cover.Models

open CFSG.ComponentClassification.CentralCover

theorem exists_local_coordinates {E : Type*} [Group E] [Group.IsPerfect E] {π : E →* P} {z : E}
    (hπ : IsCentralDoubleExt π z)
    (h15 : ∀ v : E, orderOf (π v) = 2 → fixCount (π v : Perm315) = 15 → v ^ 2 = z) :
    ∃ ι : Sp.comap π ≃* RfN, (∀ x, ((ι x).snd : P) = π x) ∧
      ((ι.symm ⟨1, 1⟩ : Sp.comap π) : E) = z ∧
      ∀ φ : E ≃* E, (∀ x, π (φ x) = betaP (π x)) →
        ∀ (x : E) (hx : π x ∈ Sp) (hφx : π (φ x) ∈ Sp), ι ⟨φ x, hφx⟩ = tauN (ι ⟨x, hx⟩) := by
  obtain ⟨u₀, k, hu₀, hu₀1, hk⟩ := Lift.exists_normCocycle_section hπ Sp
  obtain ⟨e, β, hkβ⟩ := Lift.exists_eq_smul_fN_add_coboundary hπ u₀ hu₀ hu₀1 k hk
  have he : e = 1 := by
    rcases zmod_two_cases e with rfl | rfl
    · exfalso
      have hss : eS.symm (elt 2) * eS.symm (elt 2) = 1 :=
        Lift.eS_symm_mul_self Lift.elt_two_mul_self
      have hβ1 : β 1 = 0 := by
        have h := hkβ 1 1
        rw [k.map_one_left, coboundary_apply, mul_one, zero_mul, zero_add, zmod_two_add_self,
          zero_add] at h
        exact h.symm
      have hks : k (eS.symm (elt 2)) (eS.symm (elt 2)) = 0 := by
        rw [hkβ, zero_mul, zero_add, coboundary_apply, hss, hβ1, zmod_two_add_self, add_zero]
      have hord : orderOf (π (u₀ (eS.symm (elt 2)))) = 2 := by
        rw [hu₀, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
        exact orderOf_elt_two
      have hfix : fixCount ((π (u₀ (eS.symm (elt 2))) : P) : Perm315) = 15 := by
        rw [hu₀, coe_eS_symm, incl_coe]
        exact fixCount_elt_two
      have h1 : u₀ (eS.symm (elt 2)) ^ 2 = 1 := by
        rw [sq, hk, hks, hss, hu₀1, ZMod.val_zero, pow_zero, one_mul]
      exact hπ.ne_one ((h15 _ hord hfix).symm.trans h1)
    · rfl
  subst he
  obtain ⟨ι, hι, -⟩ := hπ.exists_comap_mulEquiv_of_section Sp u₀ hu₀ fN β fun s t => by
    rw [hk, hkβ, one_mul]
  exact transport_beta hπ ι hι

theorem exists_local_coordinates_of_finite {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {π : E →* P} {z : E} (hπ : IsCentralDoubleExt π z) :
    ∃ ι : Sp.comap π ≃* RfN, (∀ x, ((ι x).snd : P) = π x) ∧
      ((ι.symm ⟨1, 1⟩ : Sp.comap π) : E) = z ∧
      ∀ φ : E ≃* E, (∀ x, π (φ x) = betaP (π x)) →
        ∀ (x : E) (hx : π x ∈ Sp) (hφx : π (φ x) ∈ Sp), ι ⟨φ x, hφx⟩ = tauN (ι ⟨x, hx⟩) := by
  obtain ⟨ι₀, hι₀, -⟩ := Lift.exists_mulEquiv_RfN (Group.isPerfect_def.1 inferInstance) hπ
  exact transport_beta hπ ι₀ hι₀

end CFSG.ComponentClassification.J2Cover.Models
