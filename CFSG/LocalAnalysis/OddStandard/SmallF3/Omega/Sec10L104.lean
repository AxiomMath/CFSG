module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L104NoSwap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L104Dich
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Da

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10L104_conj_oddCore [Finite G] {X : Subgroup G} {s : G} (hs2 : s * s = 1)
    (hs : ∀ x ∈ X, s * x * s⁻¹ ∈ X) {y : G} (hy : y ∈ oddCoreIn X) :
    s * y * s⁻¹ ∈ oddCoreIn X := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hs' : ∀ x ∈ X, s⁻¹ * x * s ∈ X := by
    intro x hx
    have e : s⁻¹ * x * s = s * x * s⁻¹ := by rw [hsi]
    rw [e]
    exact hs x hx
  set S : Subgroup G := (oddCoreIn X).map (MulAut.conj s).toMonoidHom with hS
  have hSX : S ≤ X := by
    rintro _ ⟨u, hu, rfl⟩
    exact hs u (CFSG.ClassicalInvolution.Balance.oddCoreIn_le X hu)
  have hSodd : Odd (Nat.card S) := by
    rw [hS, Subgroup.card_map_of_injective (MulAut.conj s).injective]
    exact CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X
  have hSn : ∀ k ∈ X, ∀ w ∈ S, k * w * k⁻¹ ∈ S := by
    intro k hk w hw
    obtain ⟨u, hu, rfl⟩ := hw
    refine ⟨(s⁻¹ * k * s) * u * (s⁻¹ * k * s)⁻¹,
      CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (hs' k hk) hu, ?_⟩
    show s * ((s⁻¹ * k * s) * u * (s⁻¹ * k * s)⁻¹) * s⁻¹ = k * (s * u * s⁻¹) * k⁻¹
    group
  have hnorm : X ≤ Subgroup.normalizer (S : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hSn k hk w hw, fun hw => ?_⟩
    have := hSn k⁻¹ (X.inv_mem hk) _ hw
    simpa [mul_assoc] using this
  have hle : S ≤ oddCoreIn X :=
    CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes hSX hnorm hSodd
  exact hle ⟨y, hy, rfl⟩

theorem asc82Lemma104_of (h36 : Asc82Lemma36) (hK0 : Asc82Lemma10K0) (hb : Asc82Basic10)
    (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) : Asc82Lemma104 := by
  intro G _ _ t L S z K1 K2 hctx hsc h hh hhat
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  obtain ⟨ht2, hz2, ht1, -, hne, htz⟩ := sec10D_basic hb hctx
  set s : G := h⁻¹ * t * h with hsdef
  have hs2 : s * s = 1 := by
    rw [hsdef, show (h⁻¹ * t * h) * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h by group, ht2]
    group
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hsz : s * z = z * s :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hhat).1
  have hOC : oddCoreIn (secK0 t z) ≤ centralizer (L : Set G) :=
    sec10L104_oddK0_le_centralizer hK0 h36 hP5 hC5 hb hctx
  have hKL : K1 ⊔ K2 ≤ L :=
    sup_le (hctx.pocket1.2.1.trans inf_le_left) (hctx.pocket2.2.1.trans inf_le_left)
  have hNc : ∀ n ∈ oddCoreIn (secK0 t z), ∀ a ∈ K1 ⊔ K2, n * a = a * n := fun n hn a ha =>
    (Subgroup.mem_centralizer_iff.mp (hOC hn) a (hKL ha)).symm
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_psp43 hctx.component.isQuasisimple hpsp
  have hNd : ∀ x ∈ oddCoreIn (secK0 t z), x ∈ K1 ⊔ K2 → x = 1 := by
    intro x hx hxK
    have hmem : x ∈ L ⊓ centralizer (L : Set G) := ⟨hKL hxK, hOC hx⟩
    rw [hLC] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hNodd : ∀ n ∈ oddCoreIn (secK0 t z), Odd (orderOf n) := fun n hn =>
    sec10L104_odd_orderOf hn
  have hdec := sec10L104_decomp hK0 h36 hb hctx
  have hKK0 : K1 ⊔ K2 ≤ secK0 t z := by
    obtain ⟨h1, h2, -⟩ := sec10D_K0_contains hK0 hctx
    exact sup_le h1 h2
  have hsK0 : ∀ x ∈ secK0 t z, s * x * s⁻¹ ∈ secK0 t z := fun x hx =>
    sec10D_hatCent_normalizes_K0 hK0 hctx ht2 hz2 htz ht1 hne hhat x hx
  have hsN : ∀ n ∈ oddCoreIn (secK0 t z), s * n * s⁻¹ ∈ oddCoreIn (secK0 t z) := fun n hn =>
    sec10L104_conj_oddCore hs2 hsK0 hn
  rcases sec10L104_dichotomy hP5 hpsp hctx hNc hNd hdec hKK0 hs2 hsz hsK0 hsN with hcase | hcase
  ·
    have hcomm1 : ∀ a ∈ K1, ∀ b ∈ oddCoreIn (secK0 t z), a * b = b * a := fun a ha b hb =>
      (hNc b hb a (Subgroup.mem_sup_left ha)).symm
    have hfwd : ∀ y ∈ K1 ⊔ oddCoreIn (secK0 t z),
        s * y * s⁻¹ ∈ K1 ⊔ oddCoreIn (secK0 t z) := by
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm1 hy
      obtain ⟨n, hn, k, hk, hxe⟩ := hcase a ha
      have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
      rw [e, hxe]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hn)
        (Subgroup.mem_sup_left hk)) (Subgroup.mem_sup_right (hsN b hb))
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfwd y, fun hy => ?_⟩
    have h2 := hfwd _ hy
    have e : s * (s * y * s⁻¹) * s⁻¹ = y := by
      calc s * (s * y * s⁻¹) * s⁻¹ = (s * s) * y * (s⁻¹ * s⁻¹) := by group
        _ = y := by rw [hsi, hs2]; group
    rwa [e] at h2
  ·
    exact (sec10L104_swap_false hK0 h36 hP5 hC5 hb hctx hsc hNodd hNc hNd hh hsz hcase).elim

end CFSG.OddStandard.SmallF3.Omega
