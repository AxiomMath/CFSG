module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieces
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieceTorusLift
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding.SPLMSide

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G} {z : G}
  {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}

theorem commute_glbPrimeCore_of_mem {X : Subgroup G} (hzM : z ∈ M)
    (hXC : X ≤ Subgroup.centralizer ({z} : Set G)) (hXM : X ≤ M)
    (hcent : SPLCentralizerFacts p M hzM) (hblk : SPLBlockFacts p M X) :
    ∀ x ∈ X, ∀ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)), x * o = o * x := by
  intro x hx o ho
  set O := GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) with hO
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hOM : O ≤ M := hcent.core_le
  have hcO : x * o * x⁻¹ * o⁻¹ ∈ O :=
    O.mul_mem ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_glbPrimeCore p _ (hXC hx)) o).mp ho) (O.inv_mem ho)
  have hcM : x * o * x⁻¹ * o⁻¹ ∈ M := hOM hcO
  have hxbar : mk ⟨x, hXM hx⟩ ∈ barM M X :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hnormal : (barM M X).Normal := hblk.pcore ▸ CFSG.pCore_normal
  have hbar : mk ⟨_, hcM⟩ ∈ barM M X := by
    have h2 := hnormal.conj_mem _ ((barM M X).inv_mem hxbar) (mk ⟨o, hOM ho⟩)
    have heq : mk ⟨_, hcM⟩ = mk ⟨x, hXM hx⟩ *
        (mk ⟨o, hOM ho⟩ * (mk ⟨x, hXM hx⟩)⁻¹ * (mk ⟨o, hOM ho⟩)⁻¹) := by
      change mk (⟨x, hXM hx⟩ * ⟨o, hOM ho⟩ * ⟨x, hXM hx⟩⁻¹ * ⟨o, hOM ho⟩⁻¹) = _
      simp only [map_mul, map_inv]
      group
    rw [heq]
    exact (barM M X).mul_mem hxbar h2
  have h1 : orderOf (mk ⟨_, hcM⟩) ∣ p := orderOf_dvd_of_pow_eq_one (hblk.X_elem.2 _ hbar)
  have h2 : orderOf (mk ⟨_, hcM⟩) ∣ Nat.card O := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have hpowG : (x * o * x⁻¹ * o⁻¹) ^ Nat.card O = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard O hcO)
    have hpow : (⟨_, hcM⟩ : M) ^ Nat.card O = 1 := Subtype.ext (by simpa using hpowG)
    rw [← map_pow, hpow, map_one]
  have h3 := Nat.eq_one_of_dvd_coprimes (glbPrimeCore_coprime p _) h1 h2
  rw [orderOf_eq_one_iff] at h3
  have hc2 := coe_mem_pCoreOf_two_of_mk_eq_one ⟨_, hcM⟩ h3
  have hc : x * o * x⁻¹ * o⁻¹ ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨hc2, glbPrimeCore_le p _ hcO⟩
  rw [hcent.twoCore_inf, Subgroup.mem_bot, mul_inv_eq_one] at hc
  exact mul_inv_eq_iff_eq_mul.mp hc

theorem commute_glbPrimeCore_of_torusLift {T X : Subgroup G} (hKC : KC.Normal)
    (hTp : IsPGroup p T) (hTC : T ≤ Subgroup.centralizer ({z} : Set G)) (hXT : X ≤ T)
    (hTmap : (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
    (hpair : (X.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC))
    (hXO : ∀ x ∈ X, ∀ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)), x * o = o * x)
    (htil : SPLCtildeFacts p M z Pbar KC) :
    ∀ t ∈ T, ∀ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)), t * o = o * t := by
  set C := Subgroup.centralizer ({z} : Set G)
  set O' := primeComplementCore (G := C) p
  set π := QuotientGroup.mk' O'
  set N : Subgroup C := KC.comap π ⊓ Subgroup.centralizer (O' : Set C)
  have hLn : (KC.comap π).Normal := hKC.comap π
  have hNn : N.Normal := Subgroup.normal_inf_normal _ _
  have hXN : ∀ x (hx : x ∈ X), (⟨x, hTC (hXT hx)⟩ : C) ∈ N := by
    intro x hx
    have hZ : π ⟨x, hTC (hXT hx)⟩ ∈ centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) :=
      hpair ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    refine ⟨hZ.1.2, Subgroup.mem_centralizer_iff.mpr fun h hh => Subtype.ext ?_⟩
    exact (hXO x hx h ((mem_primeComplementCore_iff_mem_glbPrimeCore p h).mp hh)).symm
  have hNmap : N.map π = KC := by
    refine htil.simple _ (Subgroup.map_le_iff_le_comap.mpr inf_le_left)
      (fun k _ n hn => (hNn.map π (QuotientGroup.mk'_surjective O')).conj_mem n hn k) ?_
    obtain ⟨a, ha, b, hb, hab⟩ := htil.nonab
    have hcomm := htil.comm a ha b hb
    rw [← hpair] at hcomm
    obtain ⟨x, hx, hxeq⟩ := hcomm
    intro hbot
    have h1 : π x ∈ N.map π := Subgroup.mem_map_of_mem _ (hXN x (Subgroup.mem_subgroupOf.mp hx))
    rw [hbot, Subgroup.mem_bot, hxeq] at h1
    exact hab (by rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1; exact h1)
  intro t ht o ho
  have htK : π ⟨t, hTC ht⟩ ∈ KC :=
    (hTmap ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ht) :
      π ⟨t, hTC ht⟩ ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC).2
  rw [← hNmap] at htK
  obtain ⟨n, hn, hnt⟩ := htK
  have hker : n⁻¹ * ⟨t, hTC ht⟩ ∈ O' := by
    rw [← QuotientGroup.ker_mk' O', MonoidHom.mem_ker, map_mul, map_inv, hnt, inv_mul_cancel]
  have hsup : (⟨t, hTC ht⟩ : C) ∈ N ⊔ O' := by
    simpa using Subgroup.mul_mem_sup hn hker
  obtain ⟨k, hk⟩ := hTp ⟨t, ht⟩
  have hk' : (⟨t, hTC ht⟩ : C) ^ p ^ k = 1 := Subtype.ext (by
    simpa using congrArg Subtype.val hk)
  have htN := mem_of_mem_sup_coprime (primeComplementCore_coprime p) hsup hk'
  have hoC : o ∈ C := glbPrimeCore_le p C ho
  have h := Subgroup.mem_centralizer_iff.mp htN.2 ⟨o, hoC⟩
    ((mem_primeComplementCore_iff_mem_glbPrimeCore p _).mpr ho)
  exact (congrArg Subtype.val h).symm

theorem eq_one_of_commute_torusLift {T : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hTmap : (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
      (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)
    (hodd : Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))))
    (htil : SPLCtildeFacts p M z Pbar KC) :
    ∀ j ∈ Subgroup.centralizer ({z} : Set G) ⊓ M, (∀ t ∈ T, j * t = t * j) → j ^ 2 = 1 →
      j = 1 := by
  intro j hj hjT hj2
  set C := Subgroup.centralizer ({z} : Set G)
  set π := QuotientGroup.mk' (primeComplementCore (G := C) p)
  set j' : C := ⟨j, hj.1⟩
  have hπj : π j' ∈ splXt0 p M z := ⟨j', Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  have hcent : ∀ y ∈ (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC, π j' * y = y * π j' := by
    intro y hy
    rw [← hTmap] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hjT _ (Subgroup.mem_subgroupOf.mp hs)))
  obtain ⟨k, hk⟩ := htil.cent_p _ hπj hcent
  have hj2' : π j' ^ 2 = 1 := by
    rw [← map_pow]
    exact (congrArg π (Subtype.ext hj2 : j' ^ 2 = 1)).trans (map_one π)
  have hcop : (p ^ k).Coprime 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
    (orderOf_dvd_of_pow_eq_one hj2')
  rw [orderOf_eq_one_iff, mk'_primeComplementCore_eq_one_iff] at h1
  have h2 : orderOf j ∣ Nat.card (GLBPrimeCore p C) :=
    Subgroup.orderOf_dvd_natCard _ h1
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hodd) h2
    (orderOf_dvd_of_pow_eq_one hj2))

end CFSG.AGLEmbedding.SPLMSide
