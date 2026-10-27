module

public import CFSG.CGT.PushingUpLit.CGT6.EmbOmegaData
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltY
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatLiftShort

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V] [Finite V]

theorem classX4_of_natSection (hV : ∀ v : V, v ^ 2 = 1) {a : ℕ} (ha : 2 ≤ a)
    {Z : Subgroup (MulAut V)} (θ : Z ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV Z) ⊥) : ClassX4 Z :=
  Or.inl (inClassX_yuHol_of_natSection hV ha θ hnat)

theorem Lift4.inClassX_of_natSection (hV : ∀ v : V, v ^ 2 = 1) {a : ℕ} (ha : 2 ≤ a)
    {H Z X : Subgroup (MulAut V)} (θ : Z ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV Z) ⊥) (h : Lift4 H Z X) :
    InClassX ↥(yuHol X) ∧ ArrowNat (yuHol Z) (yuHol X) := by
  have _ := hV
  obtain ⟨-, -, -, h4⟩ := h
  rcases h4 with h4 | ⟨k, hk, hΩ, hsplit⟩
  · exact h4
  · exfalso
    rcases hsplit with heq | ⟨-, ⟨e⟩, hcard⟩
    · subst heq
      exact (show NatOmegaN k Z from hΩ).not_equiv_alt hk ⟨θ⟩
    · obtain ⟨hm, hk2⟩ := alt_sl2_iso (by omega : 5 ≤ 2 * a + 1) hk (θ.symm.trans e)
      rw [card_commV_of_natural (by omega : 1 ≤ 2 * a + 1) θ hnat] at hcard
      have := Nat.pow_right_injective (le_refl 2) hcard
      omega

private theorem cbnSetup (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    [Group.IsPerfect ↥Y] (hZ : Subgroup.center ↥Y = ⊥) (hshort : IsShortGroup ↥(yuHol Y)) {n : ℕ}
    (halt : IsNaturalAltModule ↥(yuHol Y) n) :
    ∃ (θ : ↥Y ≃* alternatingGroup (Fin (2 * n + 1)))
      (β : ↥(commV Y) →* ↥(G6.coreMod (2 * n + 1))), Function.Surjective β ∧
      β.ker = (commV Y ⊓ fixV Y).subgroupOf (commV Y) ∧
      ∀ (x : ↥Y) (p : ↥(commV Y)) (hp : (x : MulAut V) p ∈ commV Y),
        β ⟨(x : MulAut V) p, hp⟩ = altAct (2 * n + 1) (θ x) (β p) :=
  CFSG.CGT.PushingUpLit.CGT6.altY_setup hV hZ hshort halt

theorem natSection_of_isNaturalAltModule (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    [Group.IsPerfect ↥Y] (hZ : Subgroup.center ↥Y = ⊥) (hshort : IsShortGroup ↥(yuHol Y)) {n : ℕ}
    (hn : 2 ≤ n) (halt : IsNaturalAltModule ↥(yuHol Y) n) :
    ∃ θ : ↥Y ≃* alternatingGroup (Fin (2 * n + 1)),
      IsNatSectionWith (altAct (2 * n + 1)) θ (commV Y) ⊥ := by
  obtain ⟨θ, β, hβs, hβk, hβe⟩ := cbnSetup hV hZ hshort halt
  have hC := commV_inf_fixV_eq_bot_of_quot hV (odd_two_mul_add_one n) (by omega) θ β hβs hβk hβe
  refine ⟨θ, fun x hx p hp => apply_mem_commV_self Y hx hp, β, hβs, ?_, hβe⟩
  rw [hβk, hC]

section Count

variable {N : ℕ}

private abbrev cbnE (i : Fin N) : G6.PermMod N := Multiplicative.ofAdd (Pi.single i 1)

private theorem cbnE_apply (a i : Fin N) :
    Multiplicative.toAdd (cbnE a) i = (Pi.single a 1 : Fin N → ZMod 2) i := rfl

private theorem cbn_permAct_e (σ : Equiv.Perm (Fin N)) (a : Fin N) :
    G6.permAct N σ (cbnE a) = cbnE (σ a) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp [G6.permAct_apply, cbnE_apply, Pi.single_apply, Equiv.symm_apply_eq]

private theorem cbn_permAct_allOnes (σ : Equiv.Perm (Fin N)) :
    G6.permAct N σ (G6.allOnes N) = G6.allOnes N := rfl

private theorem cbnE_mul_allOnes_mem (hN : Odd N) (a : Fin N) :
    cbnE a * G6.allOnes N ∈ G6.coreMod N := by
  rw [G6.mem_coreMod]
  simp only [toAdd_mul, Pi.add_apply, Finset.sum_add_distrib, G6.allOnes, toAdd_ofAdd]
  simp [Finset.sum_pi_single', Finset.card_univ, Fintype.card_fin]
  have h : ((N : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hN
  rw [h]
  exact CharTwo.add_self_eq_zero _

private def cbnProd (p : Fin N) (T : Finset (Fin N)) : G6.PermMod N :=
  ∏ q ∈ T, (cbnE p * cbnE q)

private theorem cbnProd_coord (p : Fin N) (T : Finset (Fin N)) {i : Fin N} (hi : i ≠ p) :
    Multiplicative.toAdd (cbnProd p T) i = if i ∈ T then 1 else 0 := by
  unfold cbnProd
  rw [toAdd_prod, Finset.sum_apply]
  simp [Pi.single_apply, hi]

private theorem cbn_card_powerset (S : Finset (Fin N)) (p : Fin N) :
    Nat.card ↥(S.erase p).powerset = 2 ^ (S.erase p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powerset]

private theorem cbnProd_injective (D : Subgroup (G6.PermMod N)) (p : Fin N) (S : Finset (Fin N))
    (hS : ∀ q ∈ S, cbnE p * cbnE q ∈ D) :
    Function.Injective (fun T : ↥(S.erase p).powerset =>
      (⟨cbnProd p T.1, Subgroup.prod_mem _ fun q hq =>
        hS q (Finset.mem_of_mem_erase (Finset.mem_powerset.mp T.2 hq))⟩ : D)) := by
  classical
  intro T T' h
  have h1 : cbnProd p T.1 = cbnProd p T'.1 := congrArg Subtype.val h
  apply Subtype.ext
  ext i
  by_cases hip : i = p
  · subst hip
    have hT : i ∉ T.1 := fun hi => (Finset.notMem_erase i S) (Finset.mem_powerset.mp T.2 hi)
    have hT' : i ∉ T'.1 := fun hi => (Finset.notMem_erase i S) (Finset.mem_powerset.mp T'.2 hi)
    simp [hT, hT']
  · have h2 := congrArg (fun x : G6.PermMod N => Multiplicative.toAdd x i) h1
    simp only [cbnProd_coord p _ hip] at h2
    by_cases a : i ∈ T.1 <;> by_cases b : i ∈ T'.1 <;> simp_all

private theorem cbn_card_ge (D : Subgroup (G6.PermMod N)) (p : Fin N) (S : Finset (Fin N))
    (hS : ∀ q ∈ S, cbnE p * cbnE q ∈ D) : 2 ^ (S.erase p).card ≤ Nat.card D := by
  classical
  have := Nat.card_le_card_of_injective _ (cbnProd_injective D p S hS)
  rwa [cbn_card_powerset] at this

private theorem cbn_supp_of_card (D : Subgroup (G6.PermMod N)) (p : Fin N) (S : Finset (Fin N))
    (hp : p ∈ S) (hS : ∀ q ∈ S, cbnE p * cbnE q ∈ D) (hcard : Nat.card D ≤ 2 ^ (S.erase p).card)
    {d : G6.PermMod N} (hd : d ∈ D) {i : Fin N} (hi : i ∉ S) : Multiplicative.toAdd d i = 0 := by
  classical
  have hbij := (cbnProd_injective D p S hS).bijective_of_nat_card_le (by
    rw [cbn_card_powerset]; exact hcard)
  obtain ⟨T, hT⟩ := hbij.2 ⟨d, hd⟩
  have hd' : cbnProd p T.1 = d := congrArg Subtype.val hT
  have hip : i ≠ p := fun h => hi (h ▸ hp)
  rw [← hd', cbnProd_coord p _ hip]
  have : i ∉ T.1 := fun h => hi (Finset.mem_of_mem_erase (Finset.mem_powerset.mp T.2 h))
  simp [this]

private theorem cbn_card_of_equiv {n : ℕ} (hn : 2 ≤ n) (G₀ : Subgroup (alternatingGroup (Fin N)))
    (e : G₀ ≃* alternatingGroup (Fin n)) : Nat.card G₀ = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]

private theorem cbn_orbit_ge {n : ℕ} (hn : 5 ≤ n) (G₀ : Subgroup (alternatingGroup (Fin N)))
    (e : G₀ ≃* alternatingGroup (Fin n)) {p : Fin N} (hp : ∃ g : G₀, g • p ≠ p) :
    n ≤ Nat.card (MulAction.orbit G₀ p) := by
  classical
  have hsimp : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  have hS : IsSimpleGroup G₀ := e.isSimpleGroup
  let ρ : G₀ →* Equiv.Perm (MulAction.orbit G₀ p) :=
    MulAction.toPermHom G₀ (MulAction.orbit G₀ p)
  have hker : ρ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg⟩ := hp
      have hgk : g ∈ ρ.ker := by rw [h]; exact Subgroup.mem_top g
      apply hg
      have := congrArg
        (fun σ : Equiv.Perm (MulAction.orbit G₀ p) => (σ ⟨p, MulAction.mem_orbit_self p⟩ : Fin N))
        (MonoidHom.mem_ker.mp hgk)
      simpa [ρ] using this
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hker
  have h1 : Nat.card G₀ ≤ (Nat.card (MulAction.orbit G₀ p)).factorial := by
    have := Nat.card_le_card_of_injective ρ hinj
    rwa [Nat.card_perm] at this
  rw [cbn_card_of_equiv (by omega) G₀ e] at h1
  by_contra hlt
  have hlt' := not_le.mp hlt
  have h2 : (Nat.card (MulAction.orbit G₀ p)).factorial ≤ (n - 1).factorial :=
    Nat.factorial_le (by omega)
  have h3 : n.factorial = n * (n - 1).factorial := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [Nat.factorial_succ]
  have h4 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h5 : 0 < (n - 1).factorial := Nat.factorial_pos _
  have h6 : n.factorial ≤ 2 * (n - 1).factorial := by omega
  rw [h3] at h6
  nlinarith

private theorem cbn_stab_of_count (hN : Odd N) {n : ℕ} (hn : 5 ≤ n)
    (G₀ : Subgroup (alternatingGroup (Fin N))) (e : G₀ ≃* alternatingGroup (Fin n))
    (D : Subgroup (G6.PermMod N))
    (hD : ∀ g : G₀, ∀ w ∈ G6.coreMod N,
      G6.permAct N ((g : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) w * w⁻¹ ∈ D)
    (hcard : Nat.card D ≤ 2 ^ (n - 1)) :
    ∃ F : Finset (Fin N), F.card = N - n ∧ G₀ = altStabilizer N F := by
  classical
  have hgen : ∀ (r : Fin N) (g : G₀), cbnE r * cbnE (g • r) ∈ D := by
    intro r g
    have hw := hD g (cbnE r * G6.allOnes N) (cbnE_mul_allOnes_mem hN r)
    have h1 : G6.permAct N ((g : alternatingGroup (Fin N)) : Equiv.Perm (Fin N))
        (cbnE r * G6.allOnes N) * (cbnE r * G6.allOnes N)⁻¹ = cbnE r * cbnE (g • r) := by
      rw [map_mul, cbn_permAct_e, cbn_permAct_allOnes]
      have key : ∀ u v w : ZMod 2, u + w + -(v + w) = v + u := by decide
      apply Multiplicative.toAdd.injective
      funext i
      simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
      exact key _ _ _
    rw [h1] at hw
    exact hw
  have hmoved : ∃ (p : Fin N) (g : G₀), g • p ≠ p := by
    by_contra hall
    have hall' : ∀ (p : Fin N) (g : G₀), g • p = p := fun p g => by
      by_contra h
      exact hall ⟨p, g, h⟩
    have h1 : G₀ = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Equiv.ext fun i => hall' i ⟨g, hg⟩)
    have hG := cbn_card_of_equiv (by omega) G₀ e
    rw [h1, Subgroup.card_bot] at hG
    have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h3 : Nat.factorial 5 ≤ n.factorial := Nat.factorial_le hn
    have h4 : Nat.factorial 5 = 120 := by decide
    omega
  obtain ⟨p, hpmoved⟩ := hmoved
  let O : Finset (Fin N) := Finset.univ.filter (· ∈ MulAction.orbit G₀ p)
  have hmemO : ∀ q, q ∈ O ↔ q ∈ MulAction.orbit G₀ p := fun q => by simp [O]
  have hpO : p ∈ O := (hmemO p).mpr (MulAction.mem_orbit_self p)
  have hOcard : O.card = Nat.card (MulAction.orbit G₀ p) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hn_le : n ≤ O.card := by
    rw [hOcard]
    exact cbn_orbit_ge hn G₀ e hpmoved
  have hgenO : ∀ q ∈ O, cbnE p * cbnE q ∈ D := by
    intro q hq
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp ((hmemO q).mp hq)
    rw [← hg]
    exact hgen p g
  have hO_le : O.card ≤ n := by
    have h1 := (cbn_card_ge D p O hgenO).trans hcard
    rw [Finset.card_erase_of_mem hpO] at h1
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    have h3 : 1 ≤ O.card := Finset.card_pos.mpr ⟨p, hpO⟩
    omega
  have hOn : O.card = n := le_antisymm hO_le hn_le
  have hsub : ∀ q : Fin N, (∃ g : G₀, g • q ≠ q) → q ∈ O := by
    intro q ⟨g, hg⟩
    by_contra hqO
    have hmem : cbnE q * cbnE (g • q) ∈ D := hgen q g
    have hc : Nat.card D ≤ 2 ^ (O.erase p).card := by
      rw [Finset.card_erase_of_mem hpO, hOn]
      exact hcard
    have h0 := cbn_supp_of_card D p O hpO hgenO hc hmem hqO
    simp only [toAdd_mul, Pi.add_apply, cbnE_apply, Pi.single_apply, ite_true] at h0
    have hne : q ≠ g • q := fun h => hg h.symm
    simp [hne] at h0
  let F : Finset (Fin N) := Finset.univ.filter fun i => ∀ g : G₀, g • i = i
  have hFO : ∀ i, i ∈ F ↔ i ∉ O := by
    intro i
    constructor
    · intro hi hiO
      have hfix : ∀ g : G₀, g • i = i := (Finset.mem_filter.mp hi).2
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp ((hmemO i).mp hiO)
      obtain ⟨h, hh⟩ := hpmoved
      apply hh
      have h1 : p = i := by
        calc p = g⁻¹ • (g • p) := (inv_smul_smul g p).symm
          _ = g⁻¹ • i := by rw [hg]
          _ = i := hfix g⁻¹
      rw [h1]
      exact hfix h
    · intro hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun g => ?_⟩
      by_contra hne
      exact hi (hsub i ⟨g, hne⟩)
  have hFcard : F.card = N - n := by
    have hF : F = Finset.univ \ O := Finset.ext fun i => by
      rw [hFO i, Finset.mem_sdiff]
      simp
    rw [hF, Finset.card_univ_sdiff, Fintype.card_fin, hOn]
  have hnN : n ≤ N := by
    have := Finset.card_le_univ O
    simpa [hOn] using this
  have hle : G₀ ≤ altStabilizer N F := by
    intro g hg
    rw [mem_altStabilizer_iff]
    intro i hi
    exact (Finset.mem_filter.mp hi).2 ⟨g, hg⟩
  refine ⟨F, hFcard, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [card_altStabilizer F (by omega), cbn_card_of_equiv (by omega) G₀ e, hFcard]
  have h : N - (N - n) = n := by omega
  rw [h]

end Count

omit [Finite V] in
theorem natSection_stab_of_natSection (hV : ∀ v : V, v ^ 2 = 1) {a b : ℕ} (ha : 2 ≤ a)
    (hb : 2 ≤ b) {L Y : Subgroup (MulAut V)} (θ : L ≃* alternatingGroup (Fin (2 * a + 1)))
    (hL : IsNatSectionWith (altAct (2 * a + 1)) θ (commV L) ⊥) (hYL : Y ≤ L)
    (φ : Y ≃* alternatingGroup (Fin (2 * b + 1)))
    (hY : IsNatSectionWith (altAct (2 * b + 1)) φ (commV Y) ⊥) :
    ∃ F : Finset (Fin (2 * a + 1)), F.card = (2 * a + 1) - (2 * b + 1) ∧
      (Y.subgroupOf L).map θ.toMonoidHom = altStabilizer (2 * a + 1) F := by
  classical
  have _ := hV
  have _ := ha
  have hN : Odd (2 * a + 1) := odd_two_mul_add_one a
  obtain ⟨hLinv, β, hβs, hβk, hβe⟩ := hL
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  let G₀ : Subgroup (alternatingGroup (Fin (2 * a + 1))) := (Y.subgroupOf L).map θ.toMonoidHom
  let e : G₀ ≃* alternatingGroup (Fin (2 * b + 1)) :=
    (Subgroup.equivMapOfInjective (Y.subgroupOf L) θ.toMonoidHom θ.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hYL).trans φ)
  let D : Subgroup (G6.PermMod (2 * a + 1)) :=
    (((commV Y).subgroupOf (commV L)).map β).map (G6.coreMod (2 * a + 1)).subtype
  have hcardD : Nat.card D = 2 ^ (2 * b) := by
    have h1 : Nat.card D = Nat.card ((commV Y).subgroupOf (commV L)) := by
      rw [Subgroup.card_map_of_injective (G6.coreMod (2 * a + 1)).subtype_injective,
        Subgroup.card_map_of_injective hβinj]
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (commV_mono hYL)).toEquiv,
      card_commV_of_natural (by omega : 1 ≤ 2 * b + 1) φ hY]
    rfl
  have hD : ∀ g : G₀, ∀ w ∈ G6.coreMod (2 * a + 1),
      G6.permAct (2 * a + 1) ((g : alternatingGroup (Fin (2 * a + 1))) :
        Equiv.Perm (Fin (2 * a + 1))) w * w⁻¹ ∈ D := by
    intro g w hw
    obtain ⟨y', hy', hy'g⟩ := g.2
    obtain ⟨p, hp⟩ := hβs ⟨w, hw⟩
    have hyY : (y' : MulAut V) ∈ Y := Subgroup.mem_subgroupOf.mp hy'
    let yp : ↥(commV L) := ⟨(y' : MulAut V) (p : V), hLinv _ y'.2 _ p.2⟩
    let cL : ↥(commV L) := yp * p⁻¹
    have hcL : cL ∈ (commV Y).subgroupOf (commV L) := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure ⟨(y' : MulAut V), hyY, (p : V), rfl⟩
    have hβc : β cL = β ⟨(y' : MulAut V) (p : V), hLinv _ y'.2 _ p.2⟩ * (β p)⁻¹ := by
      rw [map_mul, map_inv]
      rfl
    rw [hβe y' p (hLinv _ y'.2 _ p.2), hp] at hβc
    refine Subgroup.mem_map.mpr ⟨β cL, Subgroup.mem_map.mpr ⟨cL, hcL, rfl⟩, ?_⟩
    rw [hβc]
    have hg : θ y' = (g : alternatingGroup (Fin (2 * a + 1))) := hy'g
    rw [← hg]
    rfl
  obtain ⟨F, hF, hFG⟩ := cbn_stab_of_count hN (by omega : 5 ≤ 2 * b + 1) G₀ e D hD (by
    rw [hcardD]
    simp)
  exact ⟨F, hF, hFG⟩

end CFSG.CGT.PushingUpLit.CGT6
