module

public import CFSG.CGT.Foote82.T66.FaithfulBasic
import CFSG.HardMathSupport.Cooperstein.Coordinator.AltCocycle
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallModels
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82.L13Aux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.LocalAnalysis.ComponentInitial

private theorem zmod2_add_self' (a : ZMod 2) : a + a = 0 := by
  revert a; decide

private theorem zmod2_eq_add_add' (a b : ZMod 2) : a = b + (a + b) := by
  revert a b; decide

private theorem perm_inv_apply_self' {α : Type*} (σ : Perm α) (x : α) : σ⁻¹ (σ x) = x :=
  σ.symm_apply_apply x

theorem alt_hom_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (ψ : alternatingGroup α →* Multiplicative (ZMod 2)) (g : alternatingGroup α) : ψ g = 1 := by
  have h3 : ∀ c : Perm α, c.IsThreeCycle → ∀ hc : c ∈ alternatingGroup α, ψ ⟨c, hc⟩ = 1 := by
    intro c hc hcA
    have hpow : (⟨c, hcA⟩ : alternatingGroup α) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hc.orderOf]
      exact pow_orderOf_eq_one c)
    have h1 : ψ ⟨c, hcA⟩ ^ 3 = 1 := by rw [← map_pow, hpow, map_one]
    generalize ψ ⟨c, hcA⟩ = x at h1
    revert x
    decide
  have hle : Subgroup.closure {σ : Perm α | σ.IsThreeCycle} ≤
      ψ.ker.map (alternatingGroup α).subtype := by
    rw [Subgroup.closure_le]
    intro c hc
    exact ⟨⟨c, hc.mem_alternatingGroup⟩, h3 c hc _, rfl⟩
  obtain ⟨g', hg', e⟩ := hle ((closure_three_cycles_eq_alternating (α := α)).ge g.2)
  have : g' = g := Subtype.ext e
  rw [← this]
  exact hg'

theorem cocycle_apply_fixed_eq_zero' {N : ℕ} {k j : Fin N}
    (d : Perm (Fin N) → Fin N → ZMod 2)
    (hd : ∀ σ ∈ alternatingGroup (Fin N), σ k = k → ∀ τ ∈ alternatingGroup (Fin N), τ k = k →
      ∀ i, d (σ * τ) i = d σ i + d τ (σ⁻¹ i))
    {σ : Perm (Fin N)} (hσ : σ ∈ alternatingGroup (Fin N)) (hσk : σ k = k) (hσj : σ j = j) :
    d σ j = 0 := by
  classical
  set s : Finset (Fin N) := ({k, j} : Finset (Fin N))ᶜ with hs
  have hks : k ∉ s := by simp [hs]
  have hjs : j ∉ s := by simp [hs]
  have hfix : ∀ g : alternatingGroup s, ∀ i ∉ s,
      (alternatingGroup.ofSubtype s g : Perm (Fin N)) i = i := fun g i hi => by
    rw [alternatingGroup.coe_ofSubtype]
    exact Perm.ofSubtype_apply_of_not_mem _ hi
  have hfix' : ∀ g : alternatingGroup s,
      (alternatingGroup.ofSubtype s g : Perm (Fin N))⁻¹ j = j := fun g => by
    rw [Perm.inv_eq_iff_eq, hfix g j hjs]
  let ψ : alternatingGroup s →* Multiplicative (ZMod 2) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd
      (d (alternatingGroup.ofSubtype s g : Perm (Fin N)) j)) fun g g' => by
      simp only [map_mul, Subgroup.coe_mul]
      rw [hd _ (SetLike.coe_mem _) (hfix g k hks) _ (SetLike.coe_mem _) (hfix g' k hks), hfix' g]
      rfl
  have hsupp : σ.support ⊆ s := by
    intro i hi
    rw [Perm.mem_support] at hi
    simp only [hs, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hi (by rw [h]; exact hσk), fun h => hi (by rw [h]; exact hσj)⟩
  obtain ⟨g, hg⟩ := (alternatingGroup.mem_range_ofSubtype_iff s ⟨σ, hσ⟩).2 hsupp
  have hψ : ψ g = 1 := alt_hom_eq_one ψ g
  have hgσ : (alternatingGroup.ofSubtype s g : Perm (Fin N)) = σ := congrArg Subtype.val hg
  change Multiplicative.ofAdd (d (alternatingGroup.ofSubtype s g : Perm (Fin N)) j) = 1 at hψ
  rw [hgσ, ofAdd_eq_one] at hψ
  exact hψ

theorem exists_cobound_stab {N : ℕ} (hN : 5 ≤ N) (k : Fin N)
    (d : Perm (Fin N) → Fin N → ZMod 2)
    (hd : ∀ σ ∈ alternatingGroup (Fin N), σ k = k → ∀ τ ∈ alternatingGroup (Fin N), τ k = k →
      ∀ i, d (σ * τ) i = d σ i + d τ (σ⁻¹ i)) :
    ∃ x : Fin N → ZMod 2, ∀ g ∈ alternatingGroup (Fin N), g k = k → ∀ i,
      d g i = x (g⁻¹ i) + x i := by
  classical
  obtain ⟨j, hj, -, -, -⟩ := exists_ne_four hN k k k k
  have hwd : ∀ a ∈ alternatingGroup (Fin N), a k = k → ∀ b ∈ alternatingGroup (Fin N),
      b k = k → a j = b j → d b (b j) = d a (a j) := by
    intro a ha hak b hb hbk hab
    have htA : a⁻¹ * b ∈ alternatingGroup (Fin N) := mul_mem (inv_mem ha) hb
    have hak' : a⁻¹ k = k := by rw [Perm.inv_eq_iff_eq, hak]
    have htk : (a⁻¹ * b) k = k := by rw [Perm.mul_apply, hbk, hak']
    have htj : (a⁻¹ * b) j = j := by rw [Perm.mul_apply, ← hab, perm_inv_apply_self']
    have h := hd a ha hak (a⁻¹ * b) htA htk (b j)
    rw [mul_inv_cancel_left, ← hab, perm_inv_apply_self',
      cocycle_apply_fixed_eq_zero' d hd htA htk htj, add_zero] at h
    rw [← hab]
    exact h
  let x : Fin N → ZMod 2 := fun i =>
    if hi : ∃ g ∈ alternatingGroup (Fin N), g k = k ∧ g j = i then d hi.choose i else 0
  have hx : ∀ a ∈ alternatingGroup (Fin N), a k = k → x (a j) = d a (a j) := by
    intro a ha hak
    have hi : ∃ g ∈ alternatingGroup (Fin N), g k = k ∧ g j = a j := ⟨a, ha, hak, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hi.choose_spec
    simp only [x, dite_eq_left hi]
    have h := hwd a ha hak _ h1 h2 h3.symm
    rwa [h3] at h
  refine ⟨x, fun g hg hgk i => ?_⟩
  have hgk' : g⁻¹ k = k := by rw [Perm.inv_eq_iff_eq, hgk]
  by_cases hik : i = k
  · rw [hik, hgk', cocycle_apply_fixed_eq_zero' d hd hg hgk hgk, zmod2_add_self']
  obtain ⟨a, ha, hak, haj⟩ := exists_alt_fix_apply_eq hN hj hik
  have hb : g⁻¹ * a ∈ alternatingGroup (Fin N) := mul_mem (inv_mem hg) ha
  have hbk : (g⁻¹ * a) k = k := by rw [Perm.mul_apply, hak, hgk']
  have h1 := hx a ha hak
  have h2 := hx (g⁻¹ * a) hb hbk
  have h3 := hd g hg hgk (g⁻¹ * a) hb hbk i
  rw [mul_inv_cancel_left] at h3
  rw [Perm.mul_apply, haj] at h2
  rw [haj] at h1
  rw [h2, h1, h3]
  exact zmod2_eq_add_add' _ _

private theorem exists_altHeart_cobound {N : ℕ} (k : Fin N) (x : Fin N → ZMod 2) :
    ∃ m : altHeart N, ∀ g : Perm (Fin N), g k = k → ∀ i,
      altHeartCoord k m (g⁻¹ i) + altHeartCoord k m i = x (g⁻¹ i) + x i := by
  classical
  set t : ZMod 2 := (∑ i, x i) + (N : ZMod 2) * x k with ht
  set z : Fin N → ZMod 2 := fun i => x i + x k + (if i = k then t else 0) with hzdef
  have hz : z ∈ evenWeight N := by
    show (∑ i, z i) = 0
    simp only [hzdef, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Finset.sum_ite_eq', Finset.mem_univ, if_true, nsmul_eq_mul, ht]
    have h2 : ∀ a b : ZMod 2, a + b + (a + b) = 0 := by decide
    exact h2 _ _
  refine ⟨((⟨z, hz⟩ : evenWeight N) : altHeart N), fun g hgk i => ?_⟩
  rw [altHeartCoord_mk, altHeartCoord_mk]
  have hgi : g⁻¹ i = k ↔ i = k := by
    constructor
    · intro h
      rw [Perm.inv_eq_iff_eq, hgk] at h
      exact h
    · intro h
      rw [h, Perm.inv_eq_iff_eq, hgk]
  have hzk : z k = t := by
    show x k + x k + (if k = k then t else 0) = t
    rw [if_pos rfl, zmod2_add_self', zero_add]
  have hzj : ∀ j, j ≠ k → z j = x j + x k := fun j hj => by
    show x j + x k + (if j = k then t else 0) = x j + x k
    rw [if_neg hj, add_zero]
  show z (g⁻¹ i) - z k + (z i - z k) = x (g⁻¹ i) + x i
  by_cases hik : i = k
  · have hik' : g⁻¹ i = k := hgi.2 hik
    rw [hik', hik, sub_self, add_zero, zmod2_add_self']
  · have hik' : g⁻¹ i ≠ k := fun h => hik (hgi.1 h)
    rw [hzj _ hik', hzj _ hik, hzk]
    have h2 : ∀ a b c u : ZMod 2, a + c - u + (b + c - u) = a + b := by decide
    exact h2 _ _ _ _

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem eq_altAct_of_rel {n : ℕ} {σ : Perm (Fin n)} {a b : altHeart n}
    (h : ∀ x : evenWeight n, a = (x : altHeart n) → b = (evenWeightPerm σ x : altHeart n)) :
    b = altAct σ a := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [h x rfl, altAct_mk]

theorem stab_le_commutator {N : ℕ} (hN : 6 ≤ N) (k : Fin N) :
    (MulAction.stabilizer (Perm (Fin N)) k).comap (alternatingGroup (Fin N)).subtype ≤
      ⁅(MulAction.stabilizer (Perm (Fin N)) k).comap (alternatingGroup (Fin N)).subtype,
        (MulAction.stabilizer (Perm (Fin N)) k).comap (alternatingGroup (Fin N)).subtype⁆ := by
  classical
  set S := (MulAction.stabilizer (Perm (Fin N)) k).comap (alternatingGroup (Fin N)).subtype
  set s : Finset (Fin N) := ({k} : Finset (Fin N))ᶜ with hs
  have hrange : (alternatingGroup.ofSubtype s).range ≤ S := by
    rintro _ ⟨g, rfl⟩
    show (alternatingGroup.ofSubtype s g : Perm (Fin N)) • k = k
    rw [Perm.smul_def, alternatingGroup.coe_ofSubtype]
    exact Perm.ofSubtype_apply_of_not_mem _ (by simp [hs])
  have hcard : 5 ≤ Nat.card s := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hs, Finset.card_compl, Fintype.card_fin,
      Finset.card_singleton]
    omega
  have hcomm : commutator (alternatingGroup s) = ⊤ := commutator_alternatingGroup_eq_top hcard
  intro σ hσ
  have hσk : (σ : Perm (Fin N)) k = k := hσ
  have hsupp : (σ : Perm (Fin N)).support ⊆ s := by
    intro i hi
    rw [hs, Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    exact (Perm.mem_support.1 hi) hσk
  have hσr := (alternatingGroup.mem_range_ofSubtype_iff s σ).2 hsupp
  rw [MonoidHom.range_eq_map, ← hcomm, commutator_def, Subgroup.map_commutator] at hσr
  have hle : (⊤ : Subgroup (alternatingGroup s)).map (alternatingGroup.ofSubtype s) ≤ S := by
    rw [← MonoidHom.range_eq_map]
    exact hrange
  exact Subgroup.commutator_mono hle hle hσr

theorem faithfulTildeV_of_alt [Finite V] {L : Subgroup (GLV V)}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hirr : HasIrrTildeV L) {n : ℕ} (hn : 6 ≤ n)
    (hA : IsAltNaturalModule L n) : FaithfulTildeV L := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨α, hα, β, hβ, hβk, hR⟩ := hA
  have hperf := perfect_of_isQuasisimple hq
  have hcen := kT_le_center hq hirr
  set act : alternatingGroup (Fin (m + 2)) → altHeart (m + 2) → altHeart (m + 2) :=
    fun σ a => altAct (σ : Perm (Fin (m + 2))) a with hactdef
  have hact : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) w →
      β w' = act (α ℓ) (β w) := fun ℓ w w' h => eq_altAct_of_rel (hR ℓ w w' h)
  have hker : ∀ w : ↥(commSpace L ⊤), β w = 0 ↔ (w : V) ∈ fixedSpace L := fun w => by
    rw [← AddMonoidHom.mem_ker, hβk]
    rfl
  have hact1 : ∀ a, act 1 a = a := fun a => altAct_one a
  have hact0 : ∀ x, act x 0 = 0 := fun x => map_zero (altAct (x : Perm (Fin (m + 2))))
  have hkerT : α.ker ≤ kT L := ker_le_kT α β act hact hker hact1
  have hK : α.ker ≤ Subgroup.center ↥L := hkerT.trans hcen
  have hK2 : IsPGroup 2 α.ker := (kT_isPGroup hperf hcen).to_le hkerT
  set k : Fin (m + 2) := Fin.last (m + 1) with hkdef
  set S : Subgroup (alternatingGroup (Fin (m + 2))) :=
    (MulAction.stabilizer (Perm (Fin (m + 2))) k).comap (alternatingGroup (Fin (m + 2))).subtype
    with hSdef
  have hmemS : ∀ σ : alternatingGroup (Fin (m + 2)), σ ∈ S ↔ (σ : Perm (Fin (m + 2))) k = k :=
    fun σ => Iff.rfl
  set Y₀ : Subgroup ↥L := S.comap α with hY₀
  have hsplit : ∀ v : V, ∃ u ∈ commSpace L ⊤, ∀ ℓ ∈ Y₀,
      (ℓ : GLV V) (v - u) - (v - u) ∈ fixedSpace L := by
    intro v
    set s := Function.surjInv hα with hsdef
    have hs : ∀ x, α (s x) = x := Function.surjInv_eq hα
    have hcoc : ∀ {ℓ ℓ' : ↥L}, α ℓ = α ℓ' → cocy β v ℓ = cocy β v ℓ' := fun h =>
      cocy_eq_of_map_eq α β act hact hker hperf hcen hact1 hact0 v h
    let d : Perm (Fin (m + 2)) → Fin (m + 2) → ZMod 2 := fun σ =>
      if h : σ ∈ alternatingGroup (Fin (m + 2)) then altHeartCoord k (cocy β v (s ⟨σ, h⟩))
      else 0
    have hd : ∀ σ ∈ alternatingGroup (Fin (m + 2)), σ k = k →
        ∀ τ ∈ alternatingGroup (Fin (m + 2)), τ k = k → ∀ i,
          d (σ * τ) i = d σ i + d τ (σ⁻¹ i) := by
      intro σ hσ hσk τ hτ _ i
      have hστ : σ * τ ∈ alternatingGroup (Fin (m + 2)) := mul_mem hσ hτ
      simp only [d, dif_pos hστ, dif_pos hσ, dif_pos hτ]
      have e : α (s ⟨σ * τ, hστ⟩) = α (s ⟨σ, hσ⟩ * s ⟨τ, hτ⟩) := by
        rw [hs, map_mul, hs, hs]
        rfl
      rw [hcoc e, cocy_mul α β act hact v, map_add, Pi.add_apply, hs]
      rw [hactdef]
      dsimp only
      rw [altHeartCoord_altAct hσk]
    obtain ⟨x, hx⟩ := exists_cobound_stab (by omega : 5 ≤ m + 2) k d hd
    obtain ⟨a, ha⟩ := exists_altHeart_cobound k x
    refine exists_sub_mem_of_cobound α β act hact hker hβ v Y₀ a fun ℓ hℓ => ?_
    have hℓk : ((α ℓ : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) k = k :=
      (hmemS (α ℓ)).1 hℓ
    rw [hcoc (hs (α ℓ)).symm]
    apply altHeartCoord_injective k
    funext i
    have h1 := hx _ (α ℓ).2 hℓk i
    simp only [d, dif_pos (α ℓ).2] at h1
    rw [h1, map_sub, Pi.sub_apply, hactdef]
    dsimp only
    rw [altHeartCoord_altAct hℓk, ← ha _ hℓk i]
    have h2 : ∀ a b : ZMod 2, a + b = a - b := by decide
    exact h2 _ _
  have hHker : ∀ x ∈ ⁅Y₀, Y₀⁆, α x = 1 → x = 1 := by
    intro x hx hxα
    have hxT : x ∈ kT L := hkerT hxα
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨u, hu, hY⟩ := hsplit v
    have hfix := fix_of_mem_commutator (L := L) (Y := Y₀.map L.subtype)
      (by rintro _ ⟨y, -, rfl⟩; exact y.2) (v := v - u)
      (by rintro _ ⟨y, hy, rfl⟩; exact hY y hy)
    have hxmem : (x : GLV V) ∈ ⁅Y₀.map L.subtype, Y₀.map L.subtype⁆ := by
      rw [← Subgroup.map_commutator]
      exact ⟨x, hx, rfl⟩
    have h1 := hfix _ hxmem
    have h2 := kT_fix hperf hcen hxT u hu
    rw [map_sub, h2, sub_left_inj] at h1
    exact h1
  have hmapH : (⁅Y₀, Y₀⁆).map α = ⁅S, S⁆ := by
    rw [Subgroup.map_commutator, hY₀, Subgroup.map_comap_eq_self_of_surjective hα]
  have hSS : S ≤ ⁅S, S⁆ := stab_le_commutator (by omega) k
  have hliftH : ∀ c ∈ S, c ^ 3 = 1 → ∃ y ∈ ⁅Y₀, Y₀⁆, α y = c ∧ y ^ 3 = 1 := by
    intro c hc hc3
    have hcm : c ∈ (⁅Y₀, Y₀⁆).map α := by
      rw [hmapH]
      exact hSS hc
    obtain ⟨y, hy, rfl⟩ := hcm
    exact ⟨y, hy, rfl, hHker _ (Subgroup.pow_mem _ hy 3) (by rw [map_pow, hc3])⟩
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin m := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have hcS : ∀ i : Fin m, (i : ℕ) < 2 → altThreeCycle i ∈ S := by
    intro i hi
    rw [hmemS, coe_altThreeCycle, altThreeCyclePerm, Perm.mul_apply]
    have hk0 : k ≠ 0 := by simp [hkdef, Fin.ext_iff]
    have hk1 : k ≠ 1 := by
      simp only [hkdef, ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_one]
      omega
    have hki : k ≠ i.addNat 2 := by
      simp only [hkdef, ne_eq, Fin.ext_iff, Fin.val_last, Fin.coe_addNat]
      omega
    rw [swap_apply_of_ne_of_ne hk0 hk1, swap_apply_of_ne_of_ne hk0 hki]
  obtain ⟨y₀, hy₀H, hy₀α, hy₀3⟩ :=
    hliftH (altThreeCycle i₀) (hcS i₀ (by simp [hi₀])) (altThreeCycle_pow_three i₀)
  obtain ⟨y₁, hy₁H, hy₁α, hy₁3⟩ :=
    hliftH (altThreeCycle i₁) (hcS i₁ (by simp [hi₁])) (altThreeCycle_pow_three i₁)
  have hz : (y₀ * y₁) ^ 2 = 1 :=
    hHker _ (Subgroup.pow_mem _ (Subgroup.mul_mem _ hy₀H hy₁H) 2)
      (by rw [map_pow, map_mul, hy₀α, hy₁α, altThreeCycle_mul_sq h01])
  have hlift : ∀ i : Fin m, ∃ x : ↥L, α x = altThreeCycle i ∧ x ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hα (altThreeCycle i)
    obtain ⟨x, hx, hx3⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_lift_pow_three_eq_one hK hK2
      (by rw [hy]; exact altThreeCycle_pow_three i)
    exact ⟨x, hx.trans hy, hx3⟩
  choose x hxα hx3 using hlift
  have hx0 : x i₀ = y₀ :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_pow_three_eq_one_of_map_eq hK hK2 (hx3 i₀) hy₀3
      (by rw [hxα, hy₀α])
  have hx1 : x i₁ = y₁ :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_pow_three_eq_one_of_map_eq hK hK2 (hx3 i₁) hy₁3
      (by rw [hxα, hy₁α])
  have hzij : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1 := fun i j hij => by
    rw [lift_sq_eq α hα hK hK2 hxα hx3 hij h01, hx0, hx1, hz]
  have hgen : Subgroup.closure (Set.range x) = ⊤ := by
    have hmap : (Subgroup.closure (Set.range x)).map α = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have : α ∘ x = altThreeCycle := funext hxα
      rw [this, closure_altThreeCycle]
    have hsup : Subgroup.closure (Set.range x) ⊔ α.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
      (Subgroup.closure (Set.range x)) α.ker hK
    rw [hsup, ← commutator_def, hq.1] at h
    exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))
  have hcard := card_closure_le_of_carmichael m x hx3 hzij
  rw [hgen, Subgroup.card_top] at hcard
  have hP2 : Nat.card ↥L = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv]
  have hAc : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hAc]
    exact Nat.card_pos
  have hker1 : Nat.card α.ker ≤ 1 := by
    have h : (m + 2).factorial / 2 * Nat.card α.ker ≤ (m + 2).factorial / 2 * 1 := by
      rw [mul_one, ← hAc, ← hP2, hAc]
      exact hcard
    exact Nat.le_of_mul_le_mul_left h hApos
  have hbot : α.ker = ⊥ := Subgroup.eq_bot_of_card_le _ hker1
  intro ℓ hℓ hw
  have hzT : (⟨ℓ, hℓ⟩ : ↥L) ∈ kT L := hw
  have hσ : ((α ⟨ℓ, hℓ⟩ : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) = 1 := by
    refine perm_eq_one_of_altHeart_fixed (by omega) _ fun y => ?_
    obtain ⟨w, hw'⟩ := hβ (y : altHeart (m + 2))
    have hlw : ℓ (w : V) ∈ commSpace L ⊤ := invariant_commSpace_top L _ hℓ _ w.2
    have h1 := hR ⟨ℓ, hℓ⟩ w ⟨ℓ w, hlw⟩ rfl y hw'
    have h2 : β ⟨ℓ w, hlw⟩ = β w := by
      have h0 : β (⟨ℓ w, hlw⟩ - w) = 0 := (hker _).2 (hzT w w.2)
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    rw [← h1, h2, hw']
  have hmem : (⟨ℓ, hℓ⟩ : ↥L) ∈ α.ker := MonoidHom.mem_ker.2 (Subtype.ext hσ)
  rw [hbot] at hmem
  exact congrArg Subtype.val ((Subgroup.mem_bot).1 hmem)

theorem isAltNaturalModule_of_omegaPlus_three {L : Subgroup (GLV V)}
    (h : IsOmegaPlusModule L 3) : IsAltNaturalModule L 8 := by
  obtain ⟨φ, ψ, hψ⟩ := CFSG.RankThree.PartTwo.Sec19.SimsItem316Small.omegaPlusTwo_three_model
  obtain ⟨α, hα, β, hβ, hβk, hR⟩ := h
  refine ⟨(φ : ↥(omegaPlusTwo 3) →* alternatingGroup (Fin 8)).comp α, φ.surjective.comp hα,
    ψ.toAddMonoidHom.comp β, ψ.surjective.comp hβ, ?_, fun ℓ w w' hw x hx => ?_⟩
  · rw [← hβk]
    ext w
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, AddEquiv.map_eq_zero_iff]
  · have h1 := hR ℓ w w' hw
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      MonoidHom.coe_comp, MonoidHom.coe_coe] at hx ⊢
    rw [h1]
    exact hψ (α ℓ) (β w) x hx

end CFSG.CGT.Foote82.L13Aux
