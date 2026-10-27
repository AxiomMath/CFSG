module

public import CFSG.Quasithin.H13.A5ConfSpor
public import CFSG.GH74.QTGen4.DCopy.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Sporadic
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136o

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint

open KGL33 ConfSpor in

theorem factConfSpor_of_F4 (hInn : Ch1.SporadicAutInner_F4)
    (hcyc : KG68.SporadicSylowCenterCyclic) : FactConfSpor_F4 := by
  intro G _ _ K X Q a z l s hqs hs ⟨ψ⟩ hconf
  obtain ⟨hKX, hXN, hQ, haQ, hzQ, ha2, hz2, haC, hzC, ha1, hz1, haz, -, -, -, -, -⟩ := hconf
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv _ ψ.toEquiv
  have : CFSG.GH74.QTGen4.Finite4 (NativeSporadic.Carrier s) :=
    CFSG.GH74.QTGen4.Finite4.of_mulEquiv ψ
  set N := CFSG.pCore 2 ↥K with hNdef
  have hperf : commutator ↥K = ⊤ := Group.isPerfect_def.mp hqs.1

  have hN : N ≤ Subgroup.center ↥K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs (N := N) CFSG.pCore_normal with
      hN | hN
    · exfalso
      have : Group.IsPerfect ↥K := hqs.1
      have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hqs
      have hp : IsPGroup 2 ↥K := by
        have h1 : IsPGroup 2 ↥N := CFSG.pCore_isPGroup
        rw [hN] at h1
        exact h1.of_equiv Subgroup.topEquiv
      exact Group.IsPerfect.not_isNilpotent ↥K hp.isNilpotent
    · exact hN

  let ind : MulAut ↥K → MulAut (NativeSporadic.Carrier s) := fun α =>
    MulAut.congr ψ (KG68.quotAut N α)
  have hind_inj : Function.Injective ind := by
    intro α β hαβ
    have h1 : KG68.quotAut N α = KG68.quotAut N β := (MulAut.congr ψ).injective hαβ
    have h2 : KG68.quotAut N (α * β⁻¹) = 1 := by
      rw [KG68.quotAut_mul, h1, ← KG68.quotAut_mul, mul_inv_cancel, KG68.quotAut_one]
    exact mul_inv_eq_one.mp (KG68.eq_one_of_quotAut_eq_one hN hperf h2)
  have hind_apply : ∀ (α : MulAut ↥K) (x : ↥K),
      ind α (ψ (x : ↥K ⧸ N)) = ψ ((α x : ↥K) : ↥K ⧸ N) := by
    intro α x
    show ψ (KG68.quotAut N α (ψ.symm (ψ (x : ↥K ⧸ N)))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hind_mul : ∀ α β : MulAut ↥K, ind (α * β) = ind α * ind β := fun α β => by
    show MulAut.congr ψ (KG68.quotAut N (α * β)) =
      MulAut.congr ψ (KG68.quotAut N α) * MulAut.congr ψ (KG68.quotAut N β)
    rw [KG68.quotAut_mul, map_mul]
  have hind_one : ind 1 = 1 := by
    show MulAut.congr ψ (KG68.quotAut N 1) = 1
    rw [KG68.quotAut_one, map_one]

  obtain ⟨PK, hPKQ⟩ := exists_sylow_le hKX hXN hQ
  let f : ↥K →* NativeSporadic.Carrier s := ψ.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  let Qs : Sylow 2 (NativeSporadic.Carrier s) := PK.mapSurjective hf

  have hZKs : ∀ c ∈ Subgroup.center (NativeSporadic.Carrier s), ∀ k : ℕ, c ^ 2 ^ k = 1 →
      c = 1 := by
    intro c hc k hk
    have h1 : ψ.symm c ∈ Subgroup.center (↥K ⧸ N) := by
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro g
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hc (ψ g)
    have h2 : ψ.symm c ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have h3 := KG68.eq_one_of_mem_center_quot h1 h2
    simpa using congrArg ψ h3
  obtain ⟨hsq, hne⟩ := KG68.isSQTK_of_isLemma115 hs

  have key : ∀ c ∈ Q, c ^ 2 = 1 →
      (∀ t ∈ Q, c * t * c⁻¹ * t⁻¹ ∈ Subgroup.centralizer (K : Set G)) →
      ∀ hcN : c ∈ Subgroup.normalizer (K : Set G), ∃ g ∈ KG68.omegaZ (Qs : Subgroup _),
        ind (K.normalizerMonoidHom ⟨c, hcN⟩) = MulAut.conj g := by
    intro c hcQ hc2 hc hcN
    set β := ind (K.normalizerMonoidHom ⟨c, hcN⟩) with hβ
    have hfix : ∀ t ∈ (Qs : Subgroup (NativeSporadic.Carrier s)), β t = t := by
      intro t ht
      have ht' : t ∈ (PK : Subgroup ↥K).map f := ht
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ht'
      show ind (K.normalizerMonoidHom ⟨c, hcN⟩) (ψ (p : ↥K ⧸ N)) = ψ (p : ↥K ⧸ N)
      rw [hind_apply, mk_conj_eq hQ.2.1 hcN hcQ (hPKQ p hp) (hc p (hPKQ p hp))]
    have hsq' : β * β = 1 := by
      have h1 : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) *
          ⟨c, hcN⟩ = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hc2, Subgroup.coe_one])
      rw [hβ, ← hind_mul, ← map_mul, h1, map_one, hind_one]
    have hinv : ∀ x, β (β x) = x := fun x => by
      have := congrArg (fun γ : MulAut (NativeSporadic.Carrier s) => γ x) hsq'
      simpa using this
    exact exists_omegaZ_of_inner hZKs Qs β hsq' hfix
      (hInn s hsq hne (NativeSporadic.Carrier s) ⟨MulEquiv.refl _⟩ β hinv ⟨Qs, hfix⟩)
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 haQ)
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 hzQ)
  obtain ⟨ga, hga, hγa⟩ := key a haQ ha2 haC haN
  obtain ⟨gz, hgz, hγz⟩ := key z hzQ hz2 hzC hzN
  have hga1 : ga ≠ 1 := by
    rintro rfl
    rw [map_one, ← hind_one] at hγa
    exact ha1 ((normalizerMonoidHom_eq_one_iff haN).mp (hind_inj hγa))
  have hgz1 : gz ≠ 1 := by
    rintro rfl
    rw [map_one, ← hind_one] at hγz
    exact hz1 ((normalizerMonoidHom_eq_one_iff hzN).mp (hind_inj hγz))
  have hgaz : ga ≠ gz := by
    intro h
    have hN' : a * z⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ haN (Subgroup.inv_mem _ hzN)
    have he : (⟨a * z⁻¹, hN'⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨a, haN⟩ * (⟨z, hzN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ := rfl
    have h1 : ind (K.normalizerMonoidHom ⟨a * z⁻¹, hN'⟩) = ind 1 := by
      rw [he, map_mul, map_inv, hind_mul, hγa, hind_one]
      have h2 : ind (K.normalizerMonoidHom ⟨z, hzN⟩)⁻¹ = (MulAut.conj gz)⁻¹ := by
        rw [← hγz, ← mul_eq_one_iff_eq_inv, ← hind_mul, inv_mul_cancel, hind_one]
      rw [h2, h, mul_inv_cancel]
    exact haz ((normalizerMonoidHom_eq_one_iff hN').mp (hind_inj h1))
  have h1mem : (1 : NativeSporadic.Carrier s) ∈ KG68.omegaZ (Qs : Subgroup _) :=
    KG68.mem_omegaZ_of_commute Qs (fun t _ => by rw [one_mul, mul_one]) (one_mul 1)
  exact false_of_three_le (KG68.card_omegaZ_le_two (Qs : Subgroup _) (hcyc s hs Qs)) h1mem hga
    hgz (Ne.symm hga1) (Ne.symm hgz1) hgaz

end CFSG.Quasithin.H13.A5
