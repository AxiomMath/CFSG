module

public import CFSG.LieType.Steinberg.TwistedE6.Fixed
public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.LieType.Steinberg.BruhatTwist
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
import CFSG.LieType.Steinberg.PartBHalfSpace
import Mathlib.Tactic.Group
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.CurtisTits
open scoped commutatorElement

variable {k : Type*} [Field k] (θ : k →+* k)

section Sigma

theorem isTwist_sigma :
    IsTwist (e6Datum k) (e6Data_valid.nm k) (e6Data_valid.torus k) rhoPerm (sigma k θ) where
  cartan_perm := TwistTag.cartan_perm .E6
  divisible_perm _ hi := absurd hi (Set.notMem_empty _)
  map_rootGroup _ hγ _ hx :=
    sigma_mem_rootGroup_rho ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 k).1 hγ) hx
  map_n i := sigma_nm θ i
  map_torus i _ hh := by
    obtain ⟨t, rfl⟩ := (e6Data_valid.mem_torus k).1 hh
    rw [sigma_hm]
    exact e6Data_valid.hm_mem_torus k _ _

end Sigma

section Elements

variable {θ}

theorem xm_mem_twistedRootSubgroupE6_of_fixed {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hρ : rho α = α) {c : k} (hc : θ c = c) :
    e6Data_valid.xm k α c ∈ twistedRootSubgroupE6 θ (proj α) := by
  refine mem_twistedRootSubgroupE6 θ hα
    (Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k α c)) ?_
  rw [sigma_xm θ hα, twistSign_of_rho_eq hα hρ, hρ, Int.cast_one, one_mul, hc]

theorem xm_mul_xm_mem_twistedRootSubgroupE6 (hθ : ∀ c, θ (θ c) = c)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (c : k) :
    e6Data_valid.xm k α c * e6Data_valid.xm k (rho α) ((twistSign α : k) * θ c) ∈
      twistedRootSubgroupE6 θ (proj α) := by
  refine mem_twistedRootSubgroupE6 θ hα (mul_mem
    (Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k α c))
    (Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup k _ _))) ?_
  have hε : ((twistSign α : k) * (twistSign α : k)) = 1 := by
    rcases twistSign_eq_one_or α with h | h <;> simp [h]
  rw [map_mul, sigma_xm θ hα, sigma_xm θ (isRoot_rho hα), rho_rho, twistSign_rho hα, map_mul,
    map_intCast, hθ, ← mul_assoc, hε, one_mul]
  by_cases hfix : rho α = α
  · rw [hfix, ← MinData.Valid.xm_add, ← MinData.Valid.xm_add, add_comm]
  · exact (commute_of_mem_rootGroup_rho hα hfix (e6Data_valid.xm_mem_rootGroup k α c)
      (e6Data_valid.xm_mem_rootGroup k _ _)).symm.eq

variable (θ) in
abbrev twistedGenE6 : Subgroup (e6Data_valid.minGroup k) :=
  ⨆ β ∈ {β | IsRoot .F4 β}, twistedRootSubgroupE6 θ β

theorem mem_twistedGenE6 {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    {x : e6Data_valid.minGroup k} (hx : x ∈ twistedRootSubgroupE6 θ (proj α)) :
    x ∈ twistedGenE6 θ :=
  le_iSup₂_of_le (f := fun β (_ : β ∈ {β | IsRoot .F4 β}) => twistedRootSubgroupE6 θ β)
    (proj α) (isRoot_proj hα) le_rfl hx

theorem commute_xm_pair {i : Fin (Tag.rank .E6)} (hi : rhoPerm i ≠ i)
    {γ δ : Fin (Tag.rank .E6) → ℤ} (hγ : γ = Pi.single i 1 ∨ γ = -Pi.single i 1)
    (hδ : δ = Pi.single (rhoPerm i) 1 ∨ δ = -Pi.single (rhoPerm i) 1) (c d : k) :
    Commute (e6Data_valid.xm k γ c) (e6Data_valid.xm k δ d) := by
  have hα := isRoot_single .E6 i
  have hne : rho (Pi.single i 1) ≠ Pi.single i 1 := by
    rw [rho_single]
    intro h
    have h' := congrFun h (rhoPerm i)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hi] at h'
    exact one_ne_zero h'
  have h1 := not_isRoot_add_rho hα hne
  have h2 := not_isRoot_sub_rho hα hne
  have h0 := add_rho_ne_zero hα hne
  rw [rho_single] at h1 h2 h0
  have hsub0 : (Pi.single i 1 - Pi.single (rhoPerm i) 1 : Fin (Tag.rank .E6) → ℤ) ≠ 0 :=
    fun h => by
    rw [sub_eq_zero] at h
    exact hne (by rw [rho_single, h])
  have hγr : IsRoot .E6 γ := by rcases hγ with rfl | rfl; exacts [hα, isRoot_neg_single _ i]
  have hδr : IsRoot .E6 δ := by
    rcases hδ with rfl | rfl; exacts [isRoot_single _ _, isRoot_neg_single _ _]
  refine commute_xm hγr hδr ?_ ?_ c d
  · rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
    · exact h0
    · rwa [← sub_eq_add_neg]
    · rw [neg_add_eq_sub, ← neg_sub]
      exact neg_ne_zero.2 hsub0
    · rw [← neg_add]
      exact neg_ne_zero.2 h0
  · rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
    · exact h1
    · rwa [← sub_eq_add_neg]
    · rw [neg_add_eq_sub, ← neg_sub]
      exact fun h => h2 (by simpa using TagRoots.isRoot_neg h)
    · rw [← neg_add]
      exact fun h => h1 (by simpa using TagRoots.isRoot_neg h)

end Elements

section Weyl

variable {θ}

theorem xm_mem_twistedGenE6_of_fixed {i : Fin (Tag.rank .E6)} (hi : rhoPerm i = i)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ = Pi.single i 1 ∨ γ = -Pi.single i 1) {c : k}
    (hc : θ c = c) : e6Data_valid.xm k γ c ∈ twistedGenE6 θ := by
  rcases hγ with rfl | rfl
  · exact mem_twistedGenE6 (isRoot_single _ i) (xm_mem_twistedRootSubgroupE6_of_fixed
      (isRoot_single _ i) (by rw [rho_single, hi]) hc)
  · exact mem_twistedGenE6 (isRoot_neg_single _ i) (xm_mem_twistedRootSubgroupE6_of_fixed
      (isRoot_neg_single _ i) (by rw [rho_neg_single, hi]) hc)

theorem xm_mul_xm_mem_twistedGenE6 (hθ : ∀ c, θ (θ c) = c) (i : Fin (Tag.rank .E6)) (s : ℤ)
    (hs : s = 1 ∨ s = -1) (c : k) :
    e6Data_valid.xm k (s • Pi.single i 1) c *
      e6Data_valid.xm k (s • Pi.single (rhoPerm i) 1) (θ c) ∈ twistedGenE6 θ := by
  rcases hs with rfl | rfl
  · have h := xm_mul_xm_mem_twistedRootSubgroupE6 hθ (isRoot_single _ i) c
    rw [twistSign_single, rho_single, Int.cast_one, one_mul] at h
    simpa only [one_smul] using mem_twistedGenE6 (isRoot_single _ i) h
  · have h := xm_mul_xm_mem_twistedRootSubgroupE6 hθ (isRoot_neg_single _ i) c
    rw [twistSign_neg_single, rho_neg_single, Int.cast_one, one_mul] at h
    simpa only [neg_one_smul] using mem_twistedGenE6 (isRoot_neg_single _ i) h

theorem nt_mul_nt_eq {i : Fin (Tag.rank .E6)} (hi : rhoPerm i ≠ i) (s s' : kˣ) :
    e6Data_valid.nt k i s * e6Data_valid.nt k (rhoPerm i) s' =
      e6Data_valid.xm k (Pi.single i 1) s * e6Data_valid.xm k (Pi.single (rhoPerm i) 1) s' *
        (e6Data_valid.xm k (-Pi.single i 1) (-((s⁻¹ : kˣ) : k)) *
          e6Data_valid.xm k (-Pi.single (rhoPerm i) 1) (-((s'⁻¹ : kˣ) : k))) *
        (e6Data_valid.xm k (Pi.single i 1) s *
          e6Data_valid.xm k (Pi.single (rhoPerm i) 1) s') := by
  have haa' := (commute_xm_pair (k := k) hi (Or.inl rfl) (Or.inl rfl) (s : k) (s' : k)).eq
  have hba' := (commute_xm_pair (k := k) hi (Or.inr rfl) (Or.inl rfl) (-((s⁻¹ : kˣ) : k))
    (s' : k)).eq
  have hab' := (commute_xm_pair (k := k) hi (Or.inl rfl) (Or.inr rfl) (s : k)
    (-((s'⁻¹ : kˣ) : k))).eq
  rw [MinData.Valid.nt, MinData.Valid.nt]
  generalize e6Data_valid.xm k (Pi.single i 1) (s : k) = a at haa' hab' ⊢
  generalize e6Data_valid.xm k (-Pi.single i 1) (-((s⁻¹ : kˣ) : k)) = b at hba' ⊢
  generalize e6Data_valid.xm k (Pi.single (rhoPerm i) 1) (s' : k) = a' at haa' hba' ⊢
  generalize e6Data_valid.xm k (-Pi.single (rhoPerm i) 1) (-((s'⁻¹ : kˣ) : k)) = b' at hab' ⊢
  calc a * b * a * (a' * b' * a') = a * (b * (a * a') * b') * a' := by group
    _ = a * ((b * a') * (a * b')) * a' := by rw [haa']; group
    _ = a * a' * (b * b') * (a * a') := by rw [hba', hab']; group

theorem nm_mem_twistedGenE6_of_fixed {i : Fin (Tag.rank .E6)} (hi : rhoPerm i = i) :
    e6Data_valid.nm k i ∈ twistedGenE6 θ := by
  rw [MinData.Valid.nm, MinData.Valid.nt]
  refine mul_mem (mul_mem (xm_mem_twistedGenE6_of_fixed hi (Or.inl rfl) (by simp))
    (xm_mem_twistedGenE6_of_fixed hi (Or.inr rfl) (by simp)))
    (xm_mem_twistedGenE6_of_fixed hi (Or.inl rfl) (by simp))

theorem nt_mul_nt_mem_twistedGenE6 (hθ : ∀ c, θ (θ c) = c) {i : Fin (Tag.rank .E6)}
    (hi : rhoPerm i ≠ i) (s : kˣ) :
    e6Data_valid.nt k i s * e6Data_valid.nt k (rhoPerm i) (Units.map (θ : k →* k) s) ∈
      twistedGenE6 θ := by
  rw [nt_mul_nt_eq hi]
  have h1 := xm_mul_xm_mem_twistedGenE6 hθ i 1 (Or.inl rfl) (s : k)
  have h2 := xm_mul_xm_mem_twistedGenE6 hθ i (-1) (Or.inr rfl) (-((s⁻¹ : kˣ) : k))
  simp only [one_smul, neg_one_smul] at h1 h2
  have e1 : θ (s : k) = ((Units.map (θ : k →* k) s : kˣ) : k) := rfl
  have e2 : θ (-((s⁻¹ : kˣ) : k)) = -(((Units.map (θ : k →* k) s)⁻¹ : kˣ) : k) := by
    rw [map_neg, ← map_inv]
    rfl
  rw [e1] at h1
  rw [e2] at h2
  exact mul_mem (mul_mem h1 h2) h1

theorem nm_mul_nm_mem_twistedGenE6 (hθ : ∀ c, θ (θ c) = c) {i : Fin (Tag.rank .E6)}
    (hi : rhoPerm i ≠ i) :
    e6Data_valid.nm k i * e6Data_valid.nm k (rhoPerm i) ∈ twistedGenE6 θ := by
  have h := nt_mul_nt_mem_twistedGenE6 hθ hi 1
  rwa [map_one] at h

end Weyl

section Torus

variable {θ}

private abbrev e6nd (a : ℕ) (h : a < 6 := by decide) : Fin (Tag.rank .E6) := ⟨a, h⟩

theorem commute_of_mem_rankOne_pair {i : Fin (Tag.rank .E6)} (hi : rhoPerm i ≠ i)
    {x y : e6Data_valid.minGroup k} (hx : x ∈ rankOne (e6Data_valid.rootGroup k) i)
    (hy : y ∈ rankOne (e6Data_valid.rootGroup k) (rhoPerm i)) : Commute x y := by
  have hgen : ∀ γ : Fin (Tag.rank .E6) → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      rankOne (e6Data_valid.rootGroup k) (rhoPerm i) ≤
        Subgroup.centralizer (e6Data_valid.rootGroup k γ : Set (e6Data_valid.minGroup k)) := by
    intro γ hγ
    have h : ∀ δ : Fin (Tag.rank .E6) → ℤ,
        (δ = Pi.single (rhoPerm i) 1 ∨ δ = -Pi.single (rhoPerm i) 1) →
        e6Data_valid.rootGroup k δ ≤
          Subgroup.centralizer (e6Data_valid.rootGroup k γ : Set (e6Data_valid.minGroup k)) := by
      intro δ hδ y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
      obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
      exact (commute_xm_pair hi hγ hδ c d).eq
    exact sup_le (h _ (Or.inl rfl)) (h _ (Or.inr rfl))
  have hle : rankOne (e6Data_valid.rootGroup k) i ≤
      Subgroup.centralizer (rankOne (e6Data_valid.rootGroup k) (rhoPerm i) :
        Set (e6Data_valid.minGroup k)) :=
    sup_le (Subgroup.le_centralizer_iff.2 (hgen _ (Or.inl rfl)))
      (Subgroup.le_centralizer_iff.2 (hgen _ (Or.inr rfl)))
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

theorem hm_mem_twistedGenE6_of_fixed {i : Fin (Tag.rank .E6)} (hi : rhoPerm i = i) {s : kˣ}
    (hs : Units.map (θ : k →* k) s = s) : e6Data_valid.hm k i s ∈ twistedGenE6 θ := by
  have hs' : θ (s : k) = s := congrArg Units.val hs
  have hs'' : θ ((s⁻¹ : kˣ) : k) = ((s⁻¹ : kˣ) : k) :=
    congrArg Units.val (show Units.map (θ : k →* k) s⁻¹ = s⁻¹ by rw [map_inv, hs])
  rw [MinData.Valid.hm]
  refine mul_mem ?_ (inv_mem (nm_mem_twistedGenE6_of_fixed hi))
  rw [MinData.Valid.nt]
  exact mul_mem (mul_mem (xm_mem_twistedGenE6_of_fixed hi (Or.inl rfl) hs')
    (xm_mem_twistedGenE6_of_fixed hi (Or.inr rfl) (by rw [map_neg, hs''])))
    (xm_mem_twistedGenE6_of_fixed hi (Or.inl rfl) hs')

theorem hm_mul_hm_mem_twistedGenE6 (hθ : ∀ c, θ (θ c) = c) {i : Fin (Tag.rank .E6)}
    (hi : rhoPerm i ≠ i) (s : kˣ) :
    e6Data_valid.hm k i s * e6Data_valid.hm k (rhoPerm i) (Units.map (θ : k →* k) s) ∈
      twistedGenE6 θ := by
  set s' := Units.map (θ : k →* k) s
  have hc : Commute (e6Data_valid.nt k i 1)⁻¹ (e6Data_valid.nt k (rhoPerm i) s') :=
    commute_of_mem_rankOne_pair hi (inv_mem (e6Data_valid.nt_mem_rankOne k i 1))
      (e6Data_valid.nt_mem_rankOne k _ s')
  have hc' : Commute (e6Data_valid.nt k i 1) (e6Data_valid.nt k (rhoPerm i) 1) :=
    commute_of_mem_rankOne_pair hi (e6Data_valid.nt_mem_rankOne k i 1)
      (e6Data_valid.nt_mem_rankOne k _ 1)
  have e : e6Data_valid.hm k i s * e6Data_valid.hm k (rhoPerm i) s' =
      e6Data_valid.nt k i s * e6Data_valid.nt k (rhoPerm i) s' *
        (e6Data_valid.nt k i 1 * e6Data_valid.nt k (rhoPerm i) 1)⁻¹ := by
    simp only [MinData.Valid.hm]
    calc e6Data_valid.nt k i s * (e6Data_valid.nt k i 1)⁻¹ *
          (e6Data_valid.nt k (rhoPerm i) s' * (e6Data_valid.nt k (rhoPerm i) 1)⁻¹)
        = e6Data_valid.nt k i s * ((e6Data_valid.nt k i 1)⁻¹ * e6Data_valid.nt k (rhoPerm i) s') *
            (e6Data_valid.nt k (rhoPerm i) 1)⁻¹ := by group
      _ = e6Data_valid.nt k i s * (e6Data_valid.nt k (rhoPerm i) s' * (e6Data_valid.nt k i 1)⁻¹) *
            (e6Data_valid.nt k (rhoPerm i) 1)⁻¹ := by rw [hc.eq]
      _ = _ := by rw [hc'.eq]; group
  rw [e]
  refine mul_mem (nt_mul_nt_mem_twistedGenE6 hθ hi s) (inv_mem ?_)
  have h := nm_mul_nm_mem_twistedGenE6 (θ := θ) hθ hi
  rwa [MinData.Valid.nm, MinData.Valid.nm] at h

variable (k) in
private def torusElt (t : Fin (Tag.rank .E6) → kˣ) : e6Data_valid.minGroup k :=
  e6Data_valid.hm k (e6nd 0) (t (e6nd 0)) * e6Data_valid.hm k (e6nd 1) (t (e6nd 1)) *
    e6Data_valid.hm k (e6nd 2) (t (e6nd 2)) * e6Data_valid.hm k (e6nd 3) (t (e6nd 3)) *
    e6Data_valid.hm k (e6nd 4) (t (e6nd 4)) * e6Data_valid.hm k (e6nd 5) (t (e6nd 5))

private theorem charHom_eq_six (u : Fin (Tag.rank .E6) → kˣ) (n : Fin (Tag.rank .E6) → ℤ) :
    Additive.toMul (MinData.Valid.charHom k u n) = u (e6nd 0) ^ n (e6nd 0) *
      u (e6nd 1) ^ n (e6nd 1) * u (e6nd 2) ^ n (e6nd 2) *
      u (e6nd 3) ^ n (e6nd 3) * u (e6nd 4) ^ n (e6nd 4) *
      u (e6nd 5) ^ n (e6nd 5) := by
  rw [MinData.Valid.charHom_apply]
  exact Fin.prod_univ_six (fun j => u j ^ n j)

private theorem endo_torusElt (t : Fin (Tag.rank .E6) → kˣ) :
    e6Data_valid.endo k (torusElt k t) =
      diagOp fun a => ((Additive.toMul (MinData.Valid.charHom k t (e6Data.wt a)) : kˣ) : k) := by
  simp only [torusElt, MinData.Valid.endo_mul, MinData.Valid.endo_hm, MinData.hDiag, diagOp_mul]
  congr 1
  funext a
  simp only [Pi.mul_apply, charHom_eq_six, Units.val_mul]

private theorem torusElt_injective {s t : Fin (Tag.rank .E6) → kˣ}
    (h : torusElt k s = torusElt k t) : s = t := by
  have hendo := congrArg (e6Data_valid.endo k) h
  rw [endo_torusElt, endo_torusElt] at hendo
  funext i
  refine e6Data_valid.charHom_eq_of_wt k (fun a => ?_) i
  exact Additive.toMul.injective (Units.ext (congrFun (diagOp_injective hendo) a))

private theorem torusElt_mul (s t : Fin (Tag.rank .E6) → kˣ) :
    torusElt k (s * t) = torusElt k s * torusElt k t := by
  refine e6Data_valid.endo_injective k ?_
  rw [MinData.Valid.endo_mul, endo_torusElt, endo_torusElt, endo_torusElt, diagOp_mul]
  congr 1
  funext a
  simp only [Pi.mul_apply, charHom_eq_six, Units.val_mul, mul_zpow]
  ring

private theorem torusElt_one : torusElt k 1 = 1 := by
  refine e6Data_valid.endo_injective k ?_
  rw [endo_torusElt, MinData.Valid.endo_one, ← diagOp_one]
  congr 1
  funext a
  simp [charHom_eq_six]

private theorem torusElt_mulSingle (i : Fin (Tag.rank .E6)) (s : kˣ) :
    torusElt k (Pi.mulSingle i s) = e6Data_valid.hm k i s := by
  refine e6Data_valid.endo_injective k ?_
  rw [endo_torusElt, MinData.Valid.endo_hm, MinData.hDiag]
  congr 1
  funext a
  rw [MinData.Valid.charHom_apply, Finset.prod_eq_single i
    (fun l _ hl => by simp [Pi.mulSingle_eq_of_ne hl]) (by simp)]
  simp

private theorem exists_torusElt_eq {h : e6Data_valid.minGroup k}
    (hh : h ∈ ⨆ i, e6Data_valid.torus k i) : ∃ t, torusElt k t = h := by
  refine Subgroup.iSup_induction _ (C := fun x => ∃ t, torusElt k t = x) hh
    (fun i x hx => ?_) ⟨1, torusElt_one⟩ (fun x y ⟨s, hs⟩ ⟨t, ht⟩ => ⟨s * t, ?_⟩)
  · obtain ⟨s, rfl⟩ := (e6Data_valid.mem_torus k).1 hx
    exact ⟨Pi.mulSingle i s, torusElt_mulSingle i s⟩
  · rw [torusElt_mul, hs, ht]

variable (θ) in
private theorem sigma_torusElt (t : Fin (Tag.rank .E6) → kˣ) :
    sigma k θ (torusElt k t) =
      torusElt k (fun j => Units.map (θ : k →* k) (t (rhoPerm j))) := by
  simp only [torusElt, map_mul, sigma_hm]
  refine e6Data_valid.endo_injective k ?_
  simp only [MinData.Valid.endo_mul, MinData.Valid.endo_hm, MinData.hDiag, diagOp_mul]
  congr 1
  funext a
  have h0 : rhoPerm (e6nd 0) = (e6nd 5) := rfl
  have h1 : rhoPerm (e6nd 1) = (e6nd 1) := rfl
  have h2 : rhoPerm (e6nd 2) = (e6nd 4) := rfl
  have h3 : rhoPerm (e6nd 3) = (e6nd 3) := rfl
  have h4 : rhoPerm (e6nd 4) = (e6nd 2) := rfl
  have h5 : rhoPerm (e6nd 5) = (e6nd 0) := rfl
  simp only [Pi.mul_apply, h0, h1, h2, h3, h4, h5]
  ring

theorem mem_twistedGenE6_of_mem_iSup_torus (hθ : ∀ c, θ (θ c) = c)
    {h : e6Data_valid.minGroup k} (hh : h ∈ ⨆ i, e6Data_valid.torus k i)
    (hfix : sigma k θ h = h) : h ∈ twistedGenE6 θ := by
  obtain ⟨t, rfl⟩ := exists_torusElt_eq hh
  rw [sigma_torusElt] at hfix
  have hfix' := torusElt_injective hfix
  have htt : ∀ j, Units.map (θ : k →* k) (t (rhoPerm j)) = t j := fun j => congrFun hfix' j
  have h5 : t (e6nd 5) = Units.map (θ : k →* k) (t (e6nd 0)) := by
    have h := htt (e6nd 5)
    rw [show rhoPerm (e6nd 5) = e6nd 0 from rfl] at h
    exact h.symm
  have h4 : t (e6nd 4) = Units.map (θ : k →* k) (t (e6nd 2)) := by
    have h := htt (e6nd 4)
    rw [show rhoPerm (e6nd 4) = e6nd 2 from rfl] at h
    exact h.symm
  have h1 : Units.map (θ : k →* k) (t (e6nd 1)) = t (e6nd 1) := by
    have h := htt (e6nd 1)
    rwa [show rhoPerm (e6nd 1) = e6nd 1 from rfl] at h
  have h3 : Units.map (θ : k →* k) (t (e6nd 3)) = t (e6nd 3) := by
    have h := htt (e6nd 3)
    rwa [show rhoPerm (e6nd 3) = e6nd 3 from rfl] at h
  have e : torusElt k t =
      e6Data_valid.hm k (e6nd 0) (t (e6nd 0)) * e6Data_valid.hm k (e6nd 5) (t (e6nd 5)) *
        e6Data_valid.hm k (e6nd 1) (t (e6nd 1)) *
        (e6Data_valid.hm k (e6nd 2) (t (e6nd 2)) *
          e6Data_valid.hm k (e6nd 4) (t (e6nd 4))) *
        e6Data_valid.hm k (e6nd 3) (t (e6nd 3)) := by
    refine e6Data_valid.endo_injective k ?_
    simp only [torusElt, MinData.Valid.endo_mul, MinData.Valid.endo_hm, MinData.hDiag, diagOp_mul]
    congr 1
    funext a
    simp only [Pi.mul_apply]
    ring
  have hρ0 : rhoPerm (e6nd 0) ≠ e6nd 0 := by decide
  have hρ2 : rhoPerm (e6nd 2) ≠ e6nd 2 := by decide
  rw [e, h5, h4, show e6nd 5 = rhoPerm (e6nd 0) from rfl,
    show e6nd 4 = rhoPerm (e6nd 2) from rfl]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · exact hm_mul_hm_mem_twistedGenE6 hθ hρ0 _
  · exact hm_mem_twistedGenE6_of_fixed (i := e6nd 1) rfl h1
  · exact hm_mul_hm_mem_twistedGenE6 hθ hρ2 _
  · exact hm_mem_twistedGenE6_of_fixed (i := e6nd 3) rfl h3

end Torus

section Generation

private theorem weylAction_rho {w : (CFSG.LieType.RootSystem.coxeterMatrix
    (e6Datum k).isFiniteType).Group}
    (hw : weylPerm (e6Datum k).isFiniteType (isTwist_sigma (k := k) θ).cartan_perm w = w)
    (γ : Fin (Tag.rank .E6) → ℤ) :
    CFSG.LieType.RootSystem.weylAction (e6Datum k).isFiniteType w (rho γ) =
      rho (CFSG.LieType.RootSystem.weylAction (e6Datum k).isFiniteType w γ) := by
  have h := permVec_weylAction (e6Datum k).isFiniteType (isTwist_sigma (k := k) θ).cartan_perm w γ
  rw [hw] at h
  exact h.symm

private theorem rhoPerm_rhoPerm : ∀ i : Fin (Tag.rank .E6), rhoPerm (rhoPerm i) = i := by
  decide

private theorem cartan_rhoPerm :
    ∀ i : Fin (Tag.rank .E6), rhoPerm i ≠ i → Tag.cartan .E6 i (rhoPerm i) = 0 := by
  decide

private theorem ht_rho (v : Fin (Tag.rank .E6) → ℤ) : ht (rho v) = ht v := ht_permVec rhoPerm v

theorem fixedGroup_le_twistedGenE6 (hθ : ∀ c, θ (θ c) = c) :
    fixedGroup k θ ≤ twistedGenE6 θ := by
  intro g hg
  have hσg : sigma k θ g = g := hg
  have hσ := isTwist_sigma (k := k) θ
  have hct := e6Datum_isCTGroupDatum k
  have hext := e6Datum_steinbergExtras k
  obtain ⟨w, hw, b, hb, hbfix, u, hu, hufix, rfl⟩ :=
    hσ.fixed_normalForm hct hext (e6Datum_bruhatExtras k) hσg
  obtain ⟨t, htT, htfix, v, hv, hvfix, rfl⟩ := hσ.fixed_borel hct hext hb hbfix
  have hproj : ∀ Ψ : Set (Fin (Tag.rank .E6) → ℤ), (∀ α ∈ Ψ, IsRoot .E6 α) →
      ⨆ β ∈ proj '' Ψ, twistedRootSubgroupE6 θ β ≤ twistedGenE6 θ := fun Ψ hΨ =>
    iSup₂_le fun β ⟨α, hα, hαβ⟩ => hαβ ▸
      le_iSup₂_of_le (f := fun β (_ : β ∈ {β | IsRoot .F4 β}) => twistedRootSubgroupE6 θ β)
        (proj α) (isRoot_proj (hΨ α hα)) le_rfl
  have hmem := fun γ => e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 k (γ := γ)
  have hht : ∀ v, htHom (rho v) = htHom v := fun v => ht_rho v
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  ·
    exact mem_twistedGenE6_of_mem_iSup_torus hθ htT htfix
  ·
    set Ψ : Set (Fin (Tag.rank .E6) → ℤ) := {γ | γ ∈ (e6Datum k).roots ∧ 0 < ht γ}
    have hΨ : ∀ α ∈ Ψ, IsRoot .E6 α ∧ 0 < htHom α := fun α hα => ⟨(hmem α).1 hα.1, hα.2⟩
    have hcl : ∀ α ∈ Ψ, ∀ β ∈ Ψ, IsRoot .E6 (α + β) → α + β ∈ Ψ := fun α hα β hβ hr =>
      ⟨(hmem _).2 hr, by rw [ht_add]; linarith [hα.2, hβ.2]⟩
    have hρ : ∀ α ∈ Ψ, rho α ∈ Ψ := fun α hα =>
      ⟨(hmem _).2 (isRoot_rho ((hmem α).1 hα.1)), by rw [ht_rho]; exact hα.2⟩
    exact hproj Ψ (fun α hα => (hΨ α hα).1)
      (iSup_rootGroup_inf_fixedGroup_le θ hht hΨ hcl hρ (Subgroup.mem_inf.2 ⟨hv, hvfix⟩))
  ·
    exact nrep_mem_of_weylPerm_eq hct hσ.cartan_perm rhoPerm_rhoPerm cartan_rhoPerm
      (fun i hi => nm_mem_twistedGenE6_of_fixed hi)
      (fun i hi => nm_mul_nm_mem_twistedGenE6 hθ hi) hw
  ·
    set Ψ : Set (Fin (Tag.rank .E6) → ℤ) := {γ | γ ∈ (e6Datum k).roots ∧ 0 < ht γ ∧
      ht (CFSG.LieType.RootSystem.weylAction (e6Datum k).isFiniteType w γ) < 0}
    have hΨ : ∀ α ∈ Ψ, IsRoot .E6 α ∧ 0 < htHom α := fun α hα => ⟨(hmem α).1 hα.1, hα.2.1⟩
    have hcl : ∀ α ∈ Ψ, ∀ β ∈ Ψ, IsRoot .E6 (α + β) → α + β ∈ Ψ := fun α hα β hβ hr =>
      ⟨(hmem _).2 hr, by rw [ht_add]; linarith [hα.2.1, hβ.2.1],
        by rw [map_add, ht_add]; linarith [hα.2.2, hβ.2.2]⟩
    have hρ : ∀ α ∈ Ψ, rho α ∈ Ψ := by
      intro α hα
      refine ⟨(hmem _).2 (isRoot_rho ((hmem α).1 hα.1)), ?_, ?_⟩
      · rw [ht_rho]
        exact hα.2.1
      · rw [weylAction_rho θ hw, ht_rho]
        exact hα.2.2
    exact hproj Ψ (fun α hα => (hΨ α hα).1)
      (iSup_rootGroup_inf_fixedGroup_le θ hht hΨ hcl hρ (Subgroup.mem_inf.2 ⟨hu, hufix⟩))

theorem iSup_twistedDatum_rootGroup (hθ : ∀ c, θ (θ c) = c) :
    ⨆ β ∈ (twistedDatum k θ).roots, (twistedDatum k θ).rootGroup β = ⊤ := by
  rw [eq_top_iff]
  rintro g -
  rw [twistedDatum_roots]
  exact mem_iSup_twistedRootGroup_iff.2 (fixedGroup_le_twistedGenE6 θ hθ g.2)

end Generation

end CFSG.LieType.Steinberg.TwistedE6
