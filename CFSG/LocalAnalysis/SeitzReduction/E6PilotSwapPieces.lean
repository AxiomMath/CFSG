module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCover

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)

section Generic

variable {G : Type*} [Group G] {K T : Subgroup G} {t : G}

@[expose] def swapModCentralizer (hc : K.map (MulAut.conj t).toMonoidHom ≤ centralizer (K : Set G))
    (T : Subgroup G) : Subgroup G where
  carrier := {k | k ∈ K ∧ ∀ τ ∈ T, k⁻¹ * (τ * k * τ⁻¹) ∈ K.map (MulAut.conj t).toMonoidHom}
  one_mem' := ⟨one_mem _, fun τ _ => by simp [one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun τ hτ => ?_⟩
    have hza := ha' τ hτ
    have hzb := hb' τ hτ
    have hcomm : Commute (a⁻¹ * (τ * a * τ⁻¹)) b :=
      Commute.symm (mem_centralizer_iff.1 (hc hza) b hb)
    have e : (a * b)⁻¹ * (τ * (a * b) * τ⁻¹) =
        (a⁻¹ * (τ * a * τ⁻¹)) * (b⁻¹ * (τ * b * τ⁻¹)) := by
      calc (a * b)⁻¹ * (τ * (a * b) * τ⁻¹) = b⁻¹ * (a⁻¹ * (τ * a * τ⁻¹)) * (τ * b * τ⁻¹) := by
            group
        _ = (a⁻¹ * (τ * a * τ⁻¹)) * b⁻¹ * (τ * b * τ⁻¹) := by
            rw [← hcomm.inv_right.eq]
        _ = _ := by group
    rw [e]
    exact mul_mem hza hzb
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun τ hτ => ?_⟩
    have hza := ha' τ hτ
    have hcomm : Commute (a⁻¹ * (τ * a * τ⁻¹)) a :=
      Commute.symm (mem_centralizer_iff.1 (hc hza) a ha)
    have e : a⁻¹⁻¹ * (τ * a⁻¹ * τ⁻¹) = (a⁻¹ * (τ * a * τ⁻¹))⁻¹ := by
      calc a⁻¹⁻¹ * (τ * a⁻¹ * τ⁻¹) = a * (a⁻¹ * (τ * a * τ⁻¹))⁻¹ * a⁻¹ := by group
        _ = (a⁻¹ * (τ * a * τ⁻¹))⁻¹ * a * a⁻¹ := by rw [hcomm.inv_left.eq]
        _ = _ := by group
    rw [e]
    exact inv_mem hza

theorem mem_swapModCentralizer_of_mul_mem
    (hc : K.map (MulAut.conj t).toMonoidHom ≤ centralizer (K : Set G))
    (hT : T ≤ normalizer (K : Set G)) (hTt : T ≤ centralizer ({t} : Set G)) {k k' : G}
    (hk : k ∈ K) (hk' : k' ∈ K) (hx : k * (t * k' * t⁻¹) ∈ centralizer (T : Set G)) :
    k ∈ swapModCentralizer hc T := by
  refine ⟨hk, fun τ hτ => ?_⟩
  have hτt : τ * t = t * τ := mem_centralizer_singleton_iff.1 (hTt hτ)
  have hτt' : t⁻¹ * τ⁻¹ = τ⁻¹ * t⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hτt]
  have hk'τ : τ * k' * τ⁻¹ ∈ K := (mem_normalizer_iff.1 (hT hτ) k').1 hk'
  have hfix : τ * (k * (t * k' * t⁻¹)) * τ⁻¹ = k * (t * k' * t⁻¹) := by
    have h1 := mem_centralizer_iff.1 hx τ hτ
    calc τ * (k * (t * k' * t⁻¹)) * τ⁻¹ = k * (t * k' * t⁻¹) * τ * τ⁻¹ := by rw [h1]
      _ = k * (t * k' * t⁻¹) := by group
  have e1 : τ * (k * (t * k' * t⁻¹)) * τ⁻¹ =
      (τ * k * τ⁻¹) * (t * (τ * k' * τ⁻¹) * t⁻¹) := by
    calc τ * (k * (t * k' * t⁻¹)) * τ⁻¹ = (τ * k * τ⁻¹) * ((τ * t) * k' * (t⁻¹ * τ⁻¹)) := by group
      _ = (τ * k * τ⁻¹) * ((t * τ) * k' * (τ⁻¹ * t⁻¹)) := by rw [hτt, hτt']
      _ = _ := by group
  have e2 : k⁻¹ * (τ * k * τ⁻¹) = (t * k' * t⁻¹) * (t * (τ * k' * τ⁻¹) * t⁻¹)⁻¹ := by
    have h3 : (τ * k * τ⁻¹) * (t * (τ * k' * τ⁻¹) * t⁻¹) = k * (t * k' * t⁻¹) := e1.symm.trans hfix
    calc k⁻¹ * (τ * k * τ⁻¹) =
        k⁻¹ * ((τ * k * τ⁻¹) * (t * (τ * k' * τ⁻¹) * t⁻¹)) * (t * (τ * k' * τ⁻¹) * t⁻¹)⁻¹ := by
          group
      _ = k⁻¹ * (k * (t * k' * t⁻¹)) * (t * (τ * k' * τ⁻¹) * t⁻¹)⁻¹ := by rw [h3]
      _ = _ := by group
  rw [e2]
  exact mul_mem ⟨k', hk', rfl⟩ (inv_mem ⟨_, hk'τ, rfl⟩)

theorem swapPerfectCore_centralizer_le [Finite G]
    (hc : K.map (MulAut.conj t).toMonoidHom ≤ centralizer (K : Set G)) (htt : t * t = 1)
    (hT : T ≤ normalizer (K : Set G)) (hTt : T ≤ centralizer ({t} : Set G)) :
    perfectCore ((K ⊔ K.map (MulAut.conj t).toMonoidHom) ⊓ centralizer (T : Set G)) ≤
      perfectCore (K ⊓ centralizer (T : Set G)) ⊔
        (perfectCore (K ⊓ centralizer (T : Set G))).map (MulAut.conj t).toMonoidHom := by
  set A := swapModCentralizer hc T with hAdef
  have hAK : A ≤ K := fun k hk => hk.1
  have hcT : ∀ x ∈ centralizer (T : Set G), t * x * t⁻¹ ∈ centralizer (T : Set G) := by
    intro x hx
    rw [mem_centralizer_iff] at hx ⊢
    intro τ hτ
    have hτt : τ * t = t * τ := mem_centralizer_singleton_iff.1 (hTt hτ)
    have hτt' : t⁻¹ * τ⁻¹ = τ⁻¹ * t⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hτt]
    have h1 : τ * x = x * τ := hx τ hτ
    calc τ * (t * x * t⁻¹) = (τ * t) * x * t⁻¹ := by group
      _ = (t * τ) * x * t⁻¹ := by rw [hτt]
      _ = t * (τ * x) * t⁻¹ := by group
      _ = t * (x * τ) * t⁻¹ := by rw [h1]
      _ = t * x * t⁻¹ * τ := by
          calc t * (x * τ) * t⁻¹ = t * x * (τ * t⁻¹) := by group
            _ = t * x * (t⁻¹ * τ) := by
                rw [show τ * t⁻¹ = t⁻¹ * τ by
                  calc τ * t⁻¹ = t⁻¹ * (t * τ) * t⁻¹ := by group
                    _ = t⁻¹ * (τ * t) * t⁻¹ := by rw [hτt]
                    _ = t⁻¹ * τ := by group]
            _ = t * x * t⁻¹ * τ := by group
  have hstep : (K ⊔ K.map (MulAut.conj t).toMonoidHom) ⊓ centralizer (T : Set G) ≤
      A ⊔ A.map (MulAut.conj t).toMonoidHom := by
    rintro x ⟨hx, hxT⟩
    obtain ⟨k, hk, b, hb, rfl⟩ := swapExists_mul_of_mem_sup hc hx
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.1 hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxT ⊢
    have hkA : k ∈ A := mem_swapModCentralizer_of_mul_mem hc hT hTt hk hk' hxT
    have hx' : k' * (t * k * t⁻¹) ∈ centralizer (T : Set G) := by
      have h1 := hcT _ hxT
      have hcomm : Commute k' (t * k * t⁻¹) := mem_centralizer_iff.1 (hc ⟨k, hk, rfl⟩) k' hk'
      have e : t * (k * (t * k' * t⁻¹)) * t⁻¹ = k' * (t * k * t⁻¹) := by
        calc t * (k * (t * k' * t⁻¹)) * t⁻¹ = (t * k * t⁻¹) * ((t * t) * k' * (t * t)⁻¹) := by
              group
          _ = (t * k * t⁻¹) * k' := by rw [htt]; group
          _ = k' * (t * k * t⁻¹) := hcomm.eq.symm
      rwa [e] at h1
    have hk'A : k' ∈ A := mem_swapModCentralizer_of_mul_mem hc hT hTt hk' hk hx'
    exact mul_mem (mem_sup_left hkA) (mem_sup_right ⟨k', hk'A, rfl⟩)
  have hAt : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G) :=
    (map_mono hAK).trans (hc.trans (centralizer_le (SetLike.coe_subset_coe.2 hAK)))
  have h2 := swapPerfect_le_sup_perfectCore hAt (CFSG.Quasithin.perfectCore_perfect _)
    ((CFSG.Quasithin.perfectCore_le _).trans hstep)
  rw [← CFSG.Quasithin.map_perfectCore] at h2
  refine h2.trans (sup_le_sup ?_ (map_mono ?_))
  all_goals
    refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf ((CFSG.Quasithin.perfectCore_le _).trans
      hAK) ?_) (CFSG.Quasithin.perfectCore_perfect _)
    rw [← le_centralizer_iff]
    intro τ hτ
    refine swapMem_centralizer_of_perfect (Z := K ⊓ K.map (MulAut.conj t).toMonoidHom)
      (CFSG.Quasithin.perfectCore_perfect _) ?_ ?_ fun x hx => ?_
    · intro z hz
      exact centralizer_le (SetLike.coe_subset_coe.2
        ((CFSG.Quasithin.perfectCore_le _).trans hAK)) (hc hz.2)
    · intro z hz
      exact mem_centralizer_iff.2 fun w hw => mem_centralizer_iff.1 (hc hz.2) w hw.1
    · have hxA := (CFSG.Quasithin.perfectCore_le A) hx
      have hxK := hAK hxA
      exact Subgroup.mem_inf.2
        ⟨mul_mem (inv_mem hxK) ((mem_normalizer_iff.1 (hT hτ) x).1 hxK), hxA.2 τ hτ⟩

theorem swapPerfectCore_centralizer_eq [Finite G]
    (hc : K.map (MulAut.conj t).toMonoidHom ≤ centralizer (K : Set G)) (htt : t * t = 1)
    (hT : T ≤ normalizer (K : Set G)) (hTt : T ≤ centralizer ({t} : Set G)) :
    perfectCore ((K ⊔ K.map (MulAut.conj t).toMonoidHom) ⊓ centralizer (T : Set G)) =
      perfectCore (K ⊓ centralizer (T : Set G)) ⊔
        (perfectCore (K ⊓ centralizer (T : Set G))).map (MulAut.conj t).toMonoidHom := by
  refine le_antisymm (swapPerfectCore_centralizer_le hc htt hT hTt) (sup_le ?_ ?_)
  · exact CFSG.Quasithin.perfectCore_mono (inf_le_inf_right _ le_sup_left)
  · rw [CFSG.Quasithin.map_perfectCore]
    refine CFSG.Quasithin.perfectCore_mono ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨hxK, hxT⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨mem_sup_right ⟨x, hxK, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [mem_centralizer_iff] at hxT ⊢
    intro τ hτ
    have hτt : τ * t = t * τ := mem_centralizer_singleton_iff.1 (hTt hτ)
    have hτt' : τ * t⁻¹ = t⁻¹ * τ := by
      calc τ * t⁻¹ = t⁻¹ * (t * τ) * t⁻¹ := by group
        _ = t⁻¹ * (τ * t) * t⁻¹ := by rw [hτt]
        _ = t⁻¹ * τ := by group
    have h1 : τ * x = x * τ := hxT τ hτ
    calc τ * (t * x * t⁻¹) = (τ * t) * x * t⁻¹ := by group
      _ = t * (τ * x) * t⁻¹ := by rw [hτt]; group
      _ = t * (x * τ) * t⁻¹ := by rw [h1]
      _ = t * x * (τ * t⁻¹) := by group
      _ = t * x * t⁻¹ * τ := by rw [hτt']; group

end Generic

section Cover

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem odd_orderOf_of_mem_leviTorus {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {J : Finset (Fin (Tag.rank .E6))} {d : ModGL .E6 K} (hd : d ∈ leviTorus K J) :
    Odd (orderOf d) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨b, -, rfl⟩ := mem_leviTorus.1 hd
  have hpow : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 b ^ (Nat.card Kˣ) = 1 := by
    have h1 : b ^ (Nat.card Kˣ) = 1 := by
      funext i
      exact pow_card_eq_one'
    calc CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 b ^ (Nat.card Kˣ) =
        rootDiagUnitHom .E6 K (b ^ (Nat.card Kˣ)) := by rw [map_pow]; rfl
      _ = 1 := by rw [h1, map_one]
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, hK]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).2 even_two) odd_one
  exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)

omit [Finite K] [CharP K 2] in
theorem leviTorus_le_centralizer_torus {N : E6Neighbour} {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ N.nodes) : leviTorus K J ≤ centralizer (N.torus K : Set (ModGL .E6 K)) := by
  intro d hd
  rw [mem_centralizer_iff]
  intro d' hd'
  obtain ⟨b, -, rfl⟩ := mem_leviTorus.1 hd
  obtain ⟨b', -, rfl⟩ := mem_leviTorus.1 (N.torus_le_leviTorus hJ hd')
  have h1 := map_mul (rootDiagUnitHom .E6 K) b' b
  have h2 := map_mul (rootDiagUnitHom .E6 K) b b'
  rw [mul_comm b' b] at h1
  exact h1.symm.trans h2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 K} {t : G}

theorem SwapFactorCover.pieceCore_eq_sup {N : E6Neighbour} (h : SwapFactorCover e t N)
    (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) :
    pieceCore e J =
      perfectCore (h.Kc ⊓ centralizer (modelToG e (leviTorus K J) : Set G)) ⊔
        (perfectCore (h.Kc ⊓ centralizer (modelToG e (leviTorus K J) : Set G))).map
          (MulAut.conj t).toMonoidHom := by
  rw [pieceCore_eq e N hJ, ← h.sup_eq]
  refine swapPerfectCore_centralizer_eq h.le_centralizer htt (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨d, hdT, rfl⟩ := (mem_modelToG e).1 hs
    refine h.normalizer_le _ (modelToG_le_centralizer e (leviTorus_le_centralizer_torus hJ) hs) ?_
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact odd_orderOf_of_mem_leviTorus hf hK hdT
  · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL s (modelToG_le e _ hs))

end Cover

end CFSG.SeitzReduction.E6Pilot
