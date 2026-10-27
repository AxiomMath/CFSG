module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.FeitThompson.OddOrderTheorem

public section

open Subgroup
open scoped Pointwise commutatorElement

namespace CFSG.ABGLocalTools

section Abstract

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

omit [Finite H] [Fact p.Prime] in
theorem pCore_quotient_pCore_eq_bot : pCore p (H ⧸ pCore p H) = ⊥ := by
  set N : Subgroup H := pCore p H with hN
  set K : Subgroup H := (pCore p (H ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup p K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (pCore_isPGroup (G := H ⧸ N) (p := p)) ⟨_, hk⟩
    have h1 : k ^ p ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (pCore_isPGroup (G := H) (p := p)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

theorem le_pCore_of_isPGroup_of_le_fitting {D : Subgroup H} (hD : IsPGroup p D)
    (hDF : D ≤ fittingSubgroup H) : D ≤ pCore p H := by
  set F : Subgroup H := fittingSubgroup H with hF
  have hD' : IsPGroup p (D.subgroupOf F) := hD.comap_subtype
  obtain ⟨S, hS⟩ := hD'.exists_le_sylow
  have hSn : (S : Subgroup F).Normal := inferInstance
  have hSc : (S : Subgroup F).Characteristic := Sylow.characteristic_of_normal S hSn
  have hmapn : ((S : Subgroup F).map F.subtype).Normal := inferInstance
  have hle : (S : Subgroup F).map F.subtype ≤ pCore p H :=
    le_sSup ⟨hmapn, S.isPGroup'.map _⟩
  intro x hx
  exact hle ⟨⟨x, hDF hx⟩, hS hx, rfl⟩

theorem le_pCore_of_le_pCore_sup_sylow (hsolv : Group.IsSolvable H) {C : Subgroup H}
    (hC : IsPGroup p C)
    (hloc : ∀ q : ℕ, q.Prime → q ≠ p → q ∣ Nat.card H → ∃ Q : Sylow q H, ∃ M : Subgroup H,
      (Q : Subgroup H) ≤ M ∧ C ≤ (pCore p M).map M.subtype) :
    C ≤ pCore p H := by
  set N : Subgroup H := pCore p H with hN
  set π : H →* H ⧸ N := QuotientGroup.mk' N with hπ
  set D : Subgroup (H ⧸ N) := C.map π with hD
  have hDp : IsPGroup p D := hC.map π
  have hO : pCore p (H ⧸ N) = ⊥ := pCore_quotient_pCore_eq_bot
  have hsolv' : Group.IsSolvable (H ⧸ N) := inferInstance
  have hcent : ∀ q : (Nat.card (H ⧸ N)).primeFactors.attach,
      D ≤ centralizer (pCore q.1.1 (H ⧸ N) : Set (H ⧸ N)) := by
    rintro ⟨⟨q, hq⟩, -⟩
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have : Fact q.Prime := ⟨hqp⟩
    by_cases hqeq : q = p
    · subst hqeq
      rw [hO]
      intro d _
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hz
      rw [hz, one_mul, mul_one]
    have hqH : q ∣ Nat.card H :=
      (Nat.dvd_of_mem_primeFactors hq).trans (Subgroup.card_quotient_dvd_card N)
    obtain ⟨Q, M, hQM, hCM⟩ := hloc q hqp hqeq hqH
    set Qbar : Sylow q (H ⧸ N) := Q.mapSurjective (QuotientGroup.mk'_surjective N)
    have hcoreQ : pCore q (H ⧸ N) ≤ (Qbar : Subgroup (H ⧸ N)) := fitting_pCore_le_sylow Qbar
    set R : Subgroup H := (pCore p M).map M.subtype with hR
    set Rbar : Subgroup (H ⧸ N) := R.map π with hRbar
    have hRp : IsPGroup p Rbar := ((pCore_isPGroup (G := M) (p := p)).map M.subtype).map π
    have hMR : M ≤ normalizer (R : Set H) := le_normalizer_map_subtype M (pCore p M)
    have hMRbar : M.map π ≤ normalizer (Rbar : Set (H ⧸ N)) :=
      (Subgroup.map_mono hMR).trans (Subgroup.le_normalizer_map π)
    have hdisj : Rbar ⊓ pCore q (H ⧸ N) = ⊥ := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hRp
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (G := H ⧸ N) (p := q))
      apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
      rw [ha, hb]
      exact Nat.Coprime.pow a b ((Nat.coprime_primes Fact.out hqp).mpr (Ne.symm hqeq))
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hdR : d ∈ Rbar := Subgroup.map_mono hCM hd
    have hzM : z ∈ M.map π := by
      have hzQ : z ∈ (Qbar : Subgroup (H ⧸ N)) := hcoreQ hz
      rw [Sylow.coe_mapSurjective] at hzQ
      exact Subgroup.map_mono hQM hzQ
    have h1 : d⁻¹ * (z⁻¹ * d * z) ∈ Rbar := by
      refine Rbar.mul_mem (Rbar.inv_mem hdR) ?_
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hMRbar hzM)) d).mp hdR
      rwa [inv_inv] at this
    have h2 : d⁻¹ * (z⁻¹ * d * z) ∈ pCore q (H ⧸ N) := by
      have hnormal : (pCore q (H ⧸ N)).Normal := pCore_normal
      have : d⁻¹ * z⁻¹ * d ∈ pCore q (H ⧸ N) := by
        have := hnormal.conj_mem z⁻¹ (Subgroup.inv_mem _ hz) d⁻¹
        rwa [inv_inv] at this
      have := Subgroup.mul_mem _ this hz
      simpa [mul_assoc] using this
    have h3 : d⁻¹ * (z⁻¹ * d * z) = 1 := by
      have : d⁻¹ * (z⁻¹ * d * z) ∈ Rbar ⊓ pCore q (H ⧸ N) := ⟨h1, h2⟩
      rwa [hdisj, Subgroup.mem_bot] at this
    have h4 : z⁻¹ * d * z = d := (inv_mul_eq_one.mp h3).symm
    calc z * d = z * (z⁻¹ * d * z) := by rw [h4]
      _ = d * z := by group
  have hDC : D ≤ centralizer (fittingSubgroup (H ⧸ N) : Set (H ⧸ N)) :=
    subgroup_le_centralizer_fitting_of_le_centralizer_pCores hcent
  have hDF : D ≤ fittingSubgroup (H ⧸ N) :=
    hDC.trans (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv')
  have hDO : D ≤ pCore p (H ⧸ N) := le_pCore_of_isPGroup_of_le_fitting hDp hDF
  rw [hO] at hDO
  intro c hc
  have : π c ∈ (⊥ : Subgroup (H ⧸ N)) := hDO ⟨c, hc, rfl⟩
  rwa [Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this

end Abstract

section Ambient

variable {G : Type*} [Group G]

theorem map_pCore_subgroupOf {p : ℕ} {M H : Subgroup G} (hMH : M ≤ H) :
    ((pCore p (M.subgroupOf H)).map (M.subgroupOf H).subtype).map H.subtype =
      (pCore p M).map M.subtype := by
  set e : M.subgroupOf H ≃* M := Subgroup.subgroupOfEquivOfLe hMH
  rw [← pCore_map_iso p e, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem commutator_le_pCore_of_local [Finite G] {p : ℕ} [Fact p.Prime] {H T P : Subgroup G}
    (hH : Odd (Nat.card H)) (_hT : IsPGroup 2 T) (_hTH : T ≤ normalizer (H : Set G))
    (hP : IsSylowOf p P H) (hTP : T ≤ normalizer (P : Set G))
    (hloc : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∃ Q : Subgroup G, IsSylowOf q Q H ∧
      T ≤ normalizer (Q : Set G) ∧ (P : Set G) * Q = Q * P ∧
      ⁅P, T⁆ ≤ (pCore p (P ⊔ Q : Subgroup G)).map (P ⊔ Q).subtype) :
    ⁅P, T⁆ ≤ (pCore p H).map H.subtype := by
  have hPH : P ≤ H := hP.le
  have hcomm : ⁅P, T⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro x hx t ht
    rw [commutatorElement_def]
    have : t * x⁻¹ * t⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hTP ht) x⁻¹).mp (P.inv_mem hx)
    simpa [mul_assoc] using P.mul_mem hx this
  set C : Subgroup H := (⁅P, T⁆ : Subgroup G).subgroupOf H with hC
  have hCp : IsPGroup p C := (hP.isPGroup.to_le hcomm).comap_subtype
  have hsolv : Group.IsSolvable H := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hH
  have hle := le_pCore_of_le_pCore_sup_sylow hsolv hCp (by
    intro q hq hqp hqH
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hH) (even_iff_two_dvd.mpr hqH)
    obtain ⟨Q, hQ, -, -, hPQ⟩ := hloc q hq hq2 hqp
    obtain ⟨Q', hQ'⟩ := hQ
    have hQH : Q ≤ H := hQ' ▸ Subgroup.map_subtype_le _
    have hsup : P ⊔ Q ≤ H := sup_le hPH hQH
    refine ⟨Q', (P ⊔ Q).subgroupOf H, ?_, ?_⟩
    · intro x hx
      change (x : G) ∈ P ⊔ Q
      apply (le_sup_right : Q ≤ P ⊔ Q)
      rw [← hQ']
      exact Subgroup.mem_map_of_mem H.subtype hx
    · intro x hx
      have hx' : (x : G) ∈ (pCore p (P ⊔ Q : Subgroup G)).map (P ⊔ Q).subtype := hPQ hx
      rw [← map_pCore_subgroupOf hsup] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy)
  intro x hx
  exact ⟨⟨x, hPH (hcomm hx)⟩, hle hx, rfl⟩

theorem centralizer_mul_of_mul_eq [Finite G] {K S X Y : Subgroup G} (hK : Odd (Nat.card K))
    (hS : IsPGroup 2 S) (hXK : X ≤ K) (hYK : Y ≤ K)
    (hSX : S ≤ normalizer (X : Set G)) (hSY : S ≤ normalizer (Y : Set G))
    (hXY : (K : Set G) = (X : Set G) * Y) :
    ((K ⊓ centralizer (S : Set G) : Subgroup G) : Set G) =
      ((X ⊓ centralizer (S : Set G) : Subgroup G) : Set G) *
        ((Y ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
  apply Set.Subset.antisymm
  · intro c hc
    obtain ⟨hcK, hcS⟩ := hc
    have hcS' : ∀ s ∈ S, s * c * s⁻¹ = c := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff.mp hcS s hs]
      group
    let F := {z : X × Y // (z.1 : G) * (z.2 : G) = c}
    have hconjX : ∀ s : S, ∀ x : X, (s : G) * x * (s : G)⁻¹ ∈ X := fun s x =>
      (Subgroup.mem_normalizer_iff.mp (hSX s.2) x).mp x.2
    have hconjY : ∀ s : S, ∀ y : Y, (s : G) * y * (s : G)⁻¹ ∈ Y := fun s y =>
      (Subgroup.mem_normalizer_iff.mp (hSY s.2) y).mp y.2
    let act : MulAction S F :=
      { smul := fun s z => ⟨(⟨(s : G) * z.1.1 * (s : G)⁻¹, hconjX s z.1.1⟩,
          ⟨(s : G) * z.1.2 * (s : G)⁻¹, hconjY s z.1.2⟩), by
            change (s : G) * z.1.1 * (s : G)⁻¹ * ((s : G) * z.1.2 * (s : G)⁻¹) = c
            calc (s : G) * z.1.1 * (s : G)⁻¹ * ((s : G) * z.1.2 * (s : G)⁻¹)
                = (s : G) * ((z.1.1 : G) * z.1.2) * (s : G)⁻¹ := by group
              _ = c := by rw [z.2]; exact hcS' s s.2⟩
        one_smul := fun z => by
          apply Subtype.ext
          apply Prod.ext <;> apply Subtype.ext
          · change ((1 : S) : G) * z.1.1 * ((1 : S) : G)⁻¹ = z.1.1
            simp
          · change ((1 : S) : G) * z.1.2 * ((1 : S) : G)⁻¹ = z.1.2
            simp
        mul_smul := fun s t z => by
          apply Subtype.ext
          apply Prod.ext <;> apply Subtype.ext
          · change ((s * t : S) : G) * z.1.1 * ((s * t : S) : G)⁻¹ =
              (s : G) * ((t : G) * z.1.1 * (t : G)⁻¹) * (s : G)⁻¹
            simp only [Subgroup.coe_mul]
            group
          · change ((s * t : S) : G) * z.1.2 * ((s * t : S) : G)⁻¹ =
              (s : G) * ((t : G) * z.1.2 * (t : G)⁻¹) * (s : G)⁻¹
            simp only [Subgroup.coe_mul]
            group }
    have hcXY : c ∈ (X : Set G) * Y := hXY ▸ hcK
    obtain ⟨x₀, hx₀, y₀, hy₀, hc₀⟩ := hcXY
    change x₀ * y₀ = c at hc₀
    have hcardF : Nat.card F = Nat.card (X ⊓ Y : Subgroup G) := by
      apply Nat.card_congr
      exact
        { toFun := fun z => ⟨x₀⁻¹ * z.1.1, X.mul_mem (X.inv_mem hx₀) z.1.1.2, by
            obtain ⟨⟨x, y⟩, hz⟩ := z
            change x₀⁻¹ * (x : G) ∈ Y
            have hz' : (x : G) * y = c := hz
            have : x₀⁻¹ * (x : G) = y₀ * (y : G)⁻¹ := by
              calc x₀⁻¹ * (x : G) = x₀⁻¹ * ((x : G) * y) * (y : G)⁻¹ := by group
                _ = x₀⁻¹ * c * (y : G)⁻¹ := by rw [hz']
                _ = y₀ * (y : G)⁻¹ := by rw [← hc₀]; group
            rw [this]
            exact Y.mul_mem hy₀ (Y.inv_mem y.2)⟩
          invFun := fun u => ⟨(⟨x₀ * u, X.mul_mem hx₀ u.2.1⟩,
            ⟨(u : G)⁻¹ * y₀, Y.mul_mem (Y.inv_mem u.2.2) hy₀⟩), by
              change x₀ * u * ((u : G)⁻¹ * y₀) = c
              rw [← hc₀]; group⟩
          left_inv := fun z => by
            obtain ⟨⟨x, y⟩, hz⟩ := z
            have hz' : (x : G) * y = c := hz
            apply Subtype.ext
            apply Prod.ext <;> apply Subtype.ext
            · change x₀ * (x₀⁻¹ * x) = x
              group
            · change (x₀⁻¹ * (x : G))⁻¹ * y₀ = y
              calc (x₀⁻¹ * (x : G))⁻¹ * y₀ = (x : G)⁻¹ * (x₀ * y₀) := by group
                _ = (x : G)⁻¹ * ((x : G) * y) := by rw [hc₀, hz']
                _ = y := by group
          right_inv := fun u => by
            apply Subtype.ext
            change x₀⁻¹ * (x₀ * u) = u
            group }
    have hFodd : ¬ 2 ∣ Nat.card F := by
      rw [hcardF]
      intro h2
      have := h2.trans (Subgroup.card_dvd_of_le (inf_le_left.trans hXK))
      exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr this)
    obtain ⟨z, hz⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card F hFodd
    have hfx : ∀ s ∈ S, s * (z.1.1 : G) * s⁻¹ = z.1.1 := by
      intro s hs
      have := congrArg (fun w : F => (w.1.1 : G)) (hz ⟨s, hs⟩)
      exact this
    have hfy : ∀ s ∈ S, s * (z.1.2 : G) * s⁻¹ = z.1.2 := by
      intro s hs
      have := congrArg (fun w : F => (w.1.2 : G)) (hz ⟨s, hs⟩)
      exact this
    have hcen : ∀ g : G, (∀ s ∈ S, s * g * s⁻¹ = g) → g ∈ centralizer (S : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      calc s * g = s * g * s⁻¹ * s := by group
        _ = g * s := by rw [hg s hs]
    exact ⟨z.1.1, ⟨z.1.1.2, hcen _ hfx⟩, z.1.2, ⟨z.1.2.2, hcen _ hfy⟩, z.2⟩
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨K.mul_mem (hXK hx.1) (hYK hy.1), Subgroup.mul_mem _ hx.2 hy.2⟩

theorem centralizer_mul_of_hall [Finite G] {K S X Y : Subgroup G} (hK : Odd (Nat.card K))
    (hS : IsPGroup 2 S) (_hSK : S ≤ normalizer (K : Set G)) (hXK : X ≤ K) (hYK : Y ≤ K)
    (hSX : S ≤ normalizer (X : Set G)) (hSY : S ≤ normalizer (Y : Set G))
    (hXY : (K : Set G) = (X : Set G) * Y) (_hHall : Nat.Coprime (Nat.card X) (X.relIndex K)) :
    ((K ⊓ centralizer (S : Set G) : Subgroup G) : Set G) =
      ((X ⊓ centralizer (S : Set G) : Subgroup G) : Set G) *
        ((Y ⊓ centralizer (S : Set G) : Subgroup G) : Set G) :=
  centralizer_mul_of_mul_eq hK hS hXK hYK hSX hSY hXY

end Ambient

end CFSG.ABGLocalTools
