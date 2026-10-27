module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Lift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLinBase

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

namespace A3LiftHyp

variable {H Q : Subgroup G} {r : ℕ} {L : Fin r → Subgroup G} (h : A3LiftHyp H Q L)

include h

theorem card_L (i : Fin r) : Nat.card (L i) = 12 := by
  obtain ⟨-, -, -, ⟨e⟩, -⟩ := h.block i
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem card_U (i : Fin r) : Nat.card (blockQ (L i)) = 4 := by
  obtain ⟨h1, h2, -⟩ := h.block i
  rw [h1]
  exact h2

theorem exists_order3 (i : Fin r) : ∃ c ∈ L i, orderOf c = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card (L i) := by rw [h.card_L i]; norm_num
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L i)) 3 hdvd
  exact ⟨(g : G), g.2, by rw [Subgroup.orderOf_coe]; exact hg⟩

theorem gen3 (i : Fin r) {c : G} (hc : c ∈ L i) (hord : orderOf c = 3) :
    L i = Subgroup.zpowers c ⊔ blockQ (L i) := by
  have hA : Subgroup.zpowers c ⊔ blockQ (L i) ≤ L i :=
    sup_le (Subgroup.zpowers_le.2 hc) (U_le_L i)
  refine (Subgroup.eq_of_le_of_card_ge hA ?_).symm
  have h4 : 4 ∣ Nat.card ↥(Subgroup.zpowers c ⊔ blockQ (L i)) := by
    rw [← h.card_U i]
    exact Subgroup.card_dvd_of_le le_sup_right
  have h3 : 3 ∣ Nat.card ↥(Subgroup.zpowers c ⊔ blockQ (L i)) := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have h12 : 12 ∣ Nat.card ↥(Subgroup.zpowers c ⊔ blockQ (L i)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4 h3
  rw [h.card_L i]
  exact Nat.le_of_dvd Nat.card_pos h12

theorem fix_eq_one (i : Fin r) {c : G} (hc : c ∈ L i) (hord : orderOf c = 3) {v : G}
    (hv : v ∈ blockQ (L i)) (hcv : c * v = v * c) : v = 1 := by
  obtain ⟨h1, -, h3, -⟩ := h.block i
  have hvU : v ∈ blockU (L i) := h1 ▸ hv
  have hL : L i ≤ Subgroup.centralizer (({v} : Set G)) := by
    rw [h.gen3 i hc hord]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hv |> fun _ => hcv.symm
    · intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact C1.blockU_comm (h.short i) v hvU u hu
  have hvZ : v ∈ blockZ (L i) := by
    refine ⟨hvU, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp (hL hx) v (Set.mem_singleton v)
    exact this.symm
  rw [h3] at hvZ
  exact Subgroup.mem_bot.mp hvZ

omit [Finite G] in
theorem U_i_elem (i : Fin r) : IsElemAbelian 2 (blockQ (L i)) := by
  have hZ := h.U_le_Z i
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => (mem_centerTorsion_iff.mp (hZ hx)).2.2⟩
  exact (mem_centerTorsion_iff.mp (hZ b.2)).2.1 (a : G) (h.U_le_Q i a.2)

theorem disp_eq (i : Fin r) {c : G} (hc : c ∈ L i) (hord : orderOf c = 3) (x : G) :
    x ∈ blockQ (L i) ↔
      ∃ u ∈ (⨆ j, blockQ (L j) : Subgroup G), c * u * c⁻¹ * u⁻¹ = x := by
  constructor
  · intro hx
    let _ : CommGroup ↥(blockQ (L i)) := CFSG.Quasithin.commGroupOfElemAbelian (h.U_i_elem i)
    have hcn : c ∈ normalizer (blockQ (L i) : Set G) := C1.le_normalizer_blockQ _ hc
    let σ : MulAut ↥(blockQ (L i)) := (blockQ (L i)).normalizerMonoidHom ⟨c, hcn⟩
    have hσ : ∀ u : ↥(blockQ (L i)), ((σ u : ↥(blockQ (L i))) : G) = c * u * c⁻¹ := fun u =>
      Subgroup.normalizerMonoidHom_apply_apply_coe _ _ u
    have hinj : Function.Injective (dispHom σ) := by
      rw [injective_iff_map_eq_one]
      intro u hu
      have h1 : ((σ u : ↥(blockQ (L i))) : G) * (u : G)⁻¹ = 1 := congrArg Subtype.val hu
      rw [hσ] at h1
      have h2 : c * u * c⁻¹ = u := mul_inv_eq_one.mp h1
      refine Subtype.ext (h.fix_eq_one i hc hord u.2 ?_)
      calc c * (u : G) = (c * u * c⁻¹) * c := by group
        _ = u * c := by rw [h2]
    obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.mp hinj ⟨x, hx⟩
    refine ⟨(u : G), Subgroup.mem_iSup_of_mem i u.2, ?_⟩
    have h1 : ((σ u : ↥(blockQ (L i))) : G) * (u : G)⁻¹ = x := congrArg Subtype.val hu
    rw [hσ] at h1
    exact h1
  · rintro ⟨u, hu, rfl⟩
    have h1 : ⁅c, u⁆ ∈ ⁅L i, Q⁆ := Subgroup.commutator_mem_commutator hc (h.U_le_Q' hu)
    rw [Subgroup.commutator_comm, h.comm_eq i] at h1
    simpa [commutatorElement_def] using h1


omit [Finite G] h in
theorem U_i_le_U (i : Fin r) : blockQ (L i) ≤ (⨆ j, blockQ (L j) : Subgroup G) :=
  le_iSup (fun j => blockQ (L j)) i

noncomputable def c3 (i : Fin r) : G := (h.exists_order3 i).choose

theorem c3_mem (i : Fin r) : h.c3 i ∈ L i := (h.exists_order3 i).choose_spec.1

theorem c3_ord (i : Fin r) : orderOf (h.c3 i) = 3 := (h.exists_order3 i).choose_spec.2

omit [Finite G] in
theorem not_mem_Q_of_order3 {c : G} (hord : orderOf c = 3) : c ∉ Q := by
  intro hcQ
  obtain ⟨k, hk⟩ := h.Q_two ⟨c, hcQ⟩
  have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : 3 ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hk'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem L_le_of_le_sup (i j : Fin r) (hle : L j ≤ Q ⊔ L i) : L j ≤ L i := by
  have hY : Q ⊔ L i ≤ normalizer (L i : Set G) :=
    sup_le (h.Q_norm_L i) Subgroup.le_normalizer
  have hcl := NoPQuotient.closure_eq_ambient (p := 2) (h.short j).1
  rw [← hcl]
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  have hxodd : Odd (orderOf x) := Nat.not_even_iff_odd.1 fun he => hx.2 (even_iff_two_dvd.1 he)
  exact mem_of_odd_of_sup_eq (Y := Q ⊔ L i) (J := L i) (T := Q) hY le_sup_left h.Q_two
    (by rw [sup_comm]) (hle hx.1) hxodd

theorem comm_and_disjoint :
    (∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧ (∀ x ∈ H, x ^ 3 ∈ Q) ∧
      (∀ i j, i ≠ j → blockQ (L i) ⊓ blockQ (L j) = ⊥) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U : Subgroup G := ⨆ i, blockQ (L i) with hU
  have hUn := h.H_le_normalizer_U
  let _ : CommGroup ↥U := CFSG.Quasithin.commGroupOfElemAbelian h.U_elem
  let ρ : ↥H →* MulAut ↥U := CFSG.QuasithinUnique.Setup.rho U H hUn
  have hρ1 : ∀ p : ↥H, ρ p = 1 ↔ (p : G) ∈ Subgroup.centralizer (U : Set G) :=
    fun p => CFSG.QuasithinUnique.Setup.rho_eq_one_iff hUn p
  have hρQ : ∀ p : ↥H, ρ p = 1 ↔ (p : G) ∈ Q := fun p => by
    rw [hρ1]
    constructor
    · intro hp
      exact h.cent_U_le_Q p.2 (fun u hu => (Subgroup.mem_centralizer_iff.mp hp u hu).symm)
    · intro hp
      exact Subgroup.mem_centralizer_iff.mpr fun u hu => (h.Q_comm_U hu hp).symm
  let c : Fin r → ↥H := fun i => ⟨h.c3 i, h.L_le i (h.c3_mem i)⟩
  have hρc : ∀ i (u : ↥U), ((ρ (c i) u : ↥U) : G) = h.c3 i * u * (h.c3 i)⁻¹ := fun i u =>
    CFSG.QuasithinUnique.Setup.rho_apply_coe hUn (c i) u
  have hW : ∀ w : ↥U, w * w = 1 := fun w =>
    Subtype.ext (by simpa [pow_two] using h.U_elem.2 w w.2)
  have hc3 : ∀ i, orderOf (ρ (c i)) = 3 := by
    intro i
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : c i ^ 3 = 1 := Subtype.ext (by
        have := pow_orderOf_eq_one (h.c3 i)
        rwa [h.c3_ord i] at this)
      rw [this, map_one]
    · intro h1
      exact h.not_mem_Q_of_order3 (h.c3_ord i) ((hρQ (c i)).1 h1)
  have hdisp : ∀ i, dispSub (ρ (c i)) = (blockQ (L i)).subgroupOf U := by
    intro i
    ext x
    rw [mem_dispSub, Subgroup.mem_subgroupOf, h.disp_eq i (h.c3_mem i) (h.c3_ord i)]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨(w : G), w.2, ?_⟩
      have := congrArg Subtype.val hw
      simpa [hρc] using this
    · rintro ⟨u, hu, hux⟩
      refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
      simpa [hρc] using hux
  have hrk : ∀ i, Nat.card (dispSub (ρ (c i))) = 4 := by
    intro i
    rw [hdisp i, ← h.card_U i]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (U_i_le_U i)).toEquiv
  have hinj : Function.Injective fun i => Subgroup.zpowers (ρ (c i)) := by
    have key : ∀ i j, Subgroup.zpowers (ρ (c i)) = Subgroup.zpowers (ρ (c j)) → L j ≤ L i := by
      intro i j hij
      have hmem : ρ (c j) ∈ Subgroup.zpowers (ρ (c i)) := hij ▸ Subgroup.mem_zpowers _
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h1 : ρ (c j * (c i ^ n)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hn, mul_inv_cancel]
      have h2 : h.c3 j * ((h.c3 i) ^ n)⁻¹ ∈ Q := by
        have := (hρQ _).1 h1
        simpa using this
      have h3 : h.c3 j ∈ Q ⊔ L i := by
        have e : h.c3 j = (h.c3 j * ((h.c3 i) ^ n)⁻¹) * (h.c3 i) ^ n := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h2)
          (Subgroup.mem_sup_right ((L i).zpow_mem (h.c3_mem i) n))
      refine h.L_le_of_le_sup i j ?_
      rw [h.gen3 j (h.c3_mem j) (h.c3_ord j)]
      exact sup_le ((Subgroup.zpowers_le.2 h3)) (le_sup_left.trans' (h.U_le_Q j))
    intro i j hij
    have h1 := key i j hij
    have h2 := key j i hij.symm
    exact h.inj (le_antisymm h2 h1)
  have hrange : IsPGroup 3 ↥ρ.range := by
    rintro ⟨_, p, rfl⟩
    obtain ⟨k, hk⟩ := h.three p p.2
    refine ⟨k, Subtype.ext ?_⟩
    have : ρ (p ^ 3 ^ k) = 1 := (hρQ _).2 (by simpa using hk)
    simpa [map_pow] using this
  have h3 : IsPGroup 3 ↥(⨆ i, Subgroup.zpowers (ρ (c i))) :=
    hrange.to_le (iSup_le fun i => Subgroup.zpowers_le.2 ⟨c i, rfl⟩)
  have key := rank_two_three_elements (W := ↥U) hW ρ c hc3 hrk hinj h3
  have hcomm : ∀ i j, ρ (c i) * ρ (c j) = ρ (c j) * ρ (c i) := key.1
  have hind := key.2
  set D : Subgroup (MulAut ↥U) := ⨆ i, Subgroup.zpowers (ρ (c i)) with hD
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a :=
    iSup_comm_of_pairwise (fun i => Subgroup.zpowers (ρ (c i))) (fun i j a ha b hb => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((show Commute (ρ (c i)) (ρ (c j)) from hcomm i j).zpow_zpow m n).eq)
  have hDexp : ∀ g ∈ D, g ^ 3 = 1 := by
    intro g hg
    refine (Subgroup.iSup_induction (fun i => Subgroup.zpowers (ρ (c i)))
      (C := fun g => g ∈ D ∧ g ^ 3 = 1) hg ?_ ?_ ?_).2
    · intro i g hgi
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgi
      refine ⟨Subgroup.mem_iSup_of_mem i (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n), ?_⟩
      have h3 : ρ (c i) ^ 3 = 1 := by
        have := pow_orderOf_eq_one (ρ (c i))
        rwa [hc3 i] at this
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]
    · exact ⟨D.one_mem, one_pow 3⟩
    · rintro a b ⟨haD, ha⟩ ⟨hbD, hb⟩
      exact ⟨D.mul_mem haD hbD, by rw [(show Commute a b from hDcomm a haD b hbD).mul_pow, ha, hb,
        one_mul]⟩
  let D' : Subgroup G := (D.comap ρ).map H.subtype
  have hQD : Q ≤ D' := fun q hq =>
    ⟨⟨q, h.Q_le hq⟩, by
      show ρ ⟨q, h.Q_le hq⟩ ∈ D
      rw [(hρQ ⟨q, h.Q_le hq⟩).2 hq]
      exact D.one_mem, rfl⟩
  have hcD : ∀ i, h.c3 i ∈ D' := fun i =>
    ⟨c i, Subgroup.mem_iSup_of_mem i (Subgroup.mem_zpowers _), rfl⟩
  have hLD : ∀ i, L i ≤ D' := fun i => by
    rw [h.gen3 i (h.c3_mem i) (h.c3_ord i)]
    exact sup_le (Subgroup.zpowers_le.2 (hcD i)) ((h.U_le_Q i).trans hQD)
  have hHD : H ≤ D' := by
    calc H = Q ⊔ ⨆ i, L i := h.gen
      _ ≤ D' := sup_le hQD (iSup_le hLD)
  have hmemD : ∀ x (hx : x ∈ H), ρ ⟨x, hx⟩ ∈ D := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hHD hx
    have : p = ⟨x, hx⟩ := Subtype.ext hpx
    rw [this] at hp
    exact hp
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    have h1 := hDcomm _ (hmemD x hx) _ (hmemD y hy)
    have h2 : ρ (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have h3 := (hρQ _).1 h2
    simpa using h3
  · intro x hx
    have h1 := hDexp _ (hmemD x hx)
    have h2 : ρ (⟨x, hx⟩ ^ 3) = 1 := by rw [map_pow]; exact h1
    have h3 := (hρQ _).1 h2
    simpa using h3
  · intro i j hij
    have hd := hind.pairwiseDisjoint hij
    simp only [Function.onFun] at hd
    rw [hdisp i, hdisp j] at hd
    rw [eq_bot_iff]
    rintro x ⟨hxi, hxj⟩
    have hxU : x ∈ U := U_i_le_U i hxi
    have hx : (⟨x, hxU⟩ : ↥U) ∈ (blockQ (L i)).subgroupOf U ⊓ (blockQ (L j)).subgroupOf U :=
      ⟨hxi, hxj⟩
    rw [hd.eq_bot] at hx
    have := Subgroup.mem_bot.1 hx
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

end A3LiftHyp

end CFSG.QuasithinUnique.Setup.Wreath
