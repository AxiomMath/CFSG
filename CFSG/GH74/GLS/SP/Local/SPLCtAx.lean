module

public import CFSG.GH74.GLS.SP.Local.SPLCtX
public import CFSG.GH74.GLS.SP.Local.SPLCtStage2

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section CtAx

variable {G : Type} [Group G] [Finite G] {D : SPLNot1 G}

theorem A_conj_Eu (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) {u : G} (hu : SPLCtU D u)
    (hK3 : SPLCenUAt D u) {g : G} (hgu : g⁻¹ * u * g = u)
    (hgt : g⁻¹ * D.t * g = D.z * u) : ∀ a ∈ D.Act, g⁻¹ * a * g ∈ D.Eu u := by
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu.ord, pow_two] at this
  have hgu' : g * u * g⁻¹ = u := by
    calc g * u * g⁻¹ = g * (g⁻¹ * u * g) * g⁻¹ := by rw [hgu]
      _ = u := by group
  set Y : Subgroup G := D.Act.map (MulAut.conj g⁻¹).toMonoidHom with hY
  have hYmem : ∀ y, y ∈ Y ↔ ∃ a ∈ D.Act, y = g⁻¹ * a * g := by
    intro y
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, by simp⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, by simp⟩
  have hAu : ∀ a ∈ D.Act, a * u = u * a := fun a ha => hA.AI_comm a ha u hu.mem_I
  have hAt : ∀ a ∈ D.Act, a * D.t = D.t * a := fun a ha =>
    mem_centralizer_singleton_iff.mp (Act_le_Ct D ha)
  have hYle : Y ≤ D.C ⊓ centralizer ({u} : Set G) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (hYmem y).mp hy
    have hyu : (g⁻¹ * a * g) * u = u * (g⁻¹ * a * g) := by
      calc (g⁻¹ * a * g) * u = g⁻¹ * a * (g * u * g⁻¹) * g := by group
        _ = g⁻¹ * (a * u) * g := by rw [hgu']; group
        _ = g⁻¹ * (u * a) * g := by rw [hAu a ha]
        _ = g⁻¹ * u * g * (g⁻¹ * a * g) := by group
        _ = u * (g⁻¹ * a * g) := by rw [hgu]
    have hyzu : (g⁻¹ * a * g) * (D.z * u) = (D.z * u) * (g⁻¹ * a * g) := by
      calc (g⁻¹ * a * g) * (D.z * u) = (g⁻¹ * a * g) * (g⁻¹ * D.t * g) := by rw [hgt]
        _ = g⁻¹ * (a * D.t) * g := by group
        _ = g⁻¹ * (D.t * a) * g := by rw [hAt a ha]
        _ = (g⁻¹ * D.t * g) * (g⁻¹ * a * g) := by group
        _ = (D.z * u) * (g⁻¹ * a * g) := by rw [hgt]
    refine ⟨?_, mem_centralizer_singleton_iff.mpr hyu⟩
    show g⁻¹ * a * g ∈ centralizer ({D.z} : Set G)
    rw [mem_centralizer_singleton_iff]
    have hzuu : D.z * u * u = D.z := by rw [mul_assoc, hu2, mul_one]
    calc (g⁻¹ * a * g) * D.z = (g⁻¹ * a * g) * ((D.z * u) * u) := by rw [hzuu]
      _ = ((g⁻¹ * a * g) * (D.z * u)) * u := by group
      _ = ((D.z * u) * (g⁻¹ * a * g)) * u := by rw [hyzu]
      _ = (D.z * u) * ((g⁻¹ * a * g) * u) := by group
      _ = (D.z * u) * (u * (g⁻¹ * a * g)) := by rw [hyu]
      _ = ((D.z * u) * u) * (g⁻¹ * a * g) := by group
      _ = D.z * (g⁻¹ * a * g) := by rw [hzuu]
  have hYnorm : ∀ c ∈ D.C ⊓ centralizer ({u} : Set G), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := by
    intro c hc y hy
    obtain ⟨a, ha, rfl⟩ := (hYmem y).mp hy
    have hcz : c * D.z = D.z * c := mem_centralizer_singleton_iff.mp hc.1
    have hcu : c * u = u * c := mem_centralizer_singleton_iff.mp hc.2
    obtain ⟨c', hc'⟩ : ∃ c' : G, c' = g * c * g⁻¹ := ⟨_, rfl⟩
    have hc't : c' * D.t = D.t * c' := by
      have h1 : c * (D.z * u) = (D.z * u) * c := by
        calc c * (D.z * u) = (c * D.z) * u := by group
          _ = (D.z * c) * u := by rw [hcz]
          _ = D.z * (c * u) := by group
          _ = D.z * (u * c) := by rw [hcu]
          _ = (D.z * u) * c := by group
      have h2 : g * (D.z * u) * g⁻¹ = D.t := by
        calc g * (D.z * u) * g⁻¹ = g * (g⁻¹ * D.t * g) * g⁻¹ := by rw [hgt]
          _ = D.t := by group
      calc c' * D.t = (g * c * g⁻¹) * (g * (D.z * u) * g⁻¹) := by rw [hc', h2]
        _ = g * (c * (D.z * u)) * g⁻¹ := by group
        _ = g * ((D.z * u) * c) * g⁻¹ := by rw [h1]
        _ = (g * (D.z * u) * g⁻¹) * (g * c * g⁻¹) := by group
        _ = D.t * c' := by rw [h2, hc']
    have hc'u : c' * u = u * c' := by
      calc c' * u = (g * c * g⁻¹) * (g * u * g⁻¹) := by rw [hc', hgu']
        _ = g * (c * u) * g⁻¹ := by group
        _ = g * (u * c) * g⁻¹ := by rw [hcu]
        _ = (g * u * g⁻¹) * (g * c * g⁻¹) := by group
        _ = u * c' := by rw [hgu', hc']
    have hmem : c' * a * c'⁻¹ ∈ D.Act :=
      Act_normal D c' (mem_centralizer_singleton_iff.mpr hc't) a ha
    refine (hYmem _).mpr ⟨c' * a * c'⁻¹, hmem, ?_⟩
    rw [hc']; group
  have hcardY : Nat.card ↥Y = Nat.card ↥D.Act :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hYodd : Odd (Nat.card ↥Y) := by rw [hcardY]; exact Act_odd D
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨a₁, ha₁, rfl⟩ := (hYmem y₁).mp hy₁
    obtain ⟨a₂, ha₂, rfl⟩ := (hYmem y₂).mp hy₂
    calc g⁻¹ * a₁ * g * (g⁻¹ * a₂ * g) = g⁻¹ * (a₁ * a₂) * g := by group
      _ = g⁻¹ * (a₂ * a₁) * g := by rw [Act_comm D hs a₁ ha₁ a₂ ha₂]
      _ = g⁻¹ * a₂ * g * (g⁻¹ * a₁ * g) := by group
  have hYE : Y ≤ D.Eu u := hK3.fit Y hYle hYnorm hYodd hYcomm
  intro a ha
  exact hYE ((hYmem _).mpr ⟨a, ha, rfl⟩)

omit [Finite G] in
theorem SPLCtT.y_norm_T₀T₁ {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) :
    zpowers y ≤ normalizer ((T₀ ⊔ T₁ : Subgroup G) : Set G) := by
  have hnorm : ∀ g ∈ T, ∀ a ∈ T₀ ⊔ T₁, g * a * g⁻¹ ∈ T₀ ⊔ T₁ := by
    intro g hg a ha
    obtain ⟨a₀, ha₀, a₁, ha₁, rfl⟩ := mem_sup_of_commute hT.T₀_T₁ ha
    have : g * (a₀ * a₁) * g⁻¹ = (g * a₀ * g⁻¹) * (g * a₁ * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (hT.T₀_norm g hg a₀ ha₀) (hT.T₁_norm g hg a₁ ha₁)
  rw [zpowers_le, mem_normalizer_iff]
  intro a
  constructor
  · exact fun ha => hnorm y hT.y_mem a ha
  · intro ha
    have h1 := hnorm y⁻¹ (T.inv_mem hT.y_mem) _ ha
    have e : y⁻¹ * (y * a * y⁻¹) * y⁻¹⁻¹ = a := by group
    rwa [e] at h1

theorem ct_Ax (hs : SPLSetup D.toSPLNot0) (hA : SPLCtA D) {u : G} (hud : SPLCtUD D u)
    {T T₀ T₁ : Subgroup G} {y : G} (hT : SPLCtT D T T₀ T₁ y) {x : G} (hxY : x ∈ T₀ ⊔ zpowers y)
    (hxo : orderOf x = 2 ^ (D.n - 1)) (hxt : x ^ (2 ^ (D.n - 2)) = D.t) :
    ∀ a ∈ D.Act, a * x = x * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  obtain ⟨g, hgu, hgz, hgt⟩ := hud.d
  obtain ⟨R, hRC, hRE, hRcyc, hRp, hRcard, hzR⟩ := hud.K3.torus
  have hu := hud.U
  have hAEu := A_conj_Eu hs hA hu hud.K3 hgu hgt
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu.ord, pow_two] at this
  have hgu' : g * u * g⁻¹ = u := by
    calc g * u * g⁻¹ = g * (g⁻¹ * u * g) * g⁻¹ := by rw [hgu]
      _ = u := by group
  have hgz' : g * D.z * g⁻¹ = D.t * u := by
    have h1 : D.t = (g * D.z * g⁻¹) * u := by
      calc D.t = g * (g⁻¹ * D.t * g) * g⁻¹ := by group
        _ = g * (D.z * u) * g⁻¹ := by rw [hgt]
        _ = (g * D.z * g⁻¹) * (g * u * g⁻¹) := by group
        _ = (g * D.z * g⁻¹) * u := by rw [hgu']
    calc g * D.z * g⁻¹ = (g * D.z * g⁻¹) * (u * u) := by rw [hu2, mul_one]
      _ = ((g * D.z * g⁻¹) * u) * u := by group
      _ = D.t * u := by rw [← h1]
  set Q : Subgroup G := R.map (MulAut.conj g).toMonoidHom with hQ
  have hQp : IsPGroup 2 Q := hRp.map _
  have hQcard : Nat.card ↥Q = 2 ^ (D.n - 1) := by
    rw [hQ, Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hRcard
  have hQcyc : IsCyclic ↥Q := by
    have : IsCyclic ↥(R.map (MulAut.conj g).toMonoidHom) :=
      isCyclic_of_surjective (Subgroup.equivMapOfInjective R _ (MulAut.conj g).injective).toMonoidHom
        (Subgroup.equivMapOfInjective R _ (MulAut.conj g).injective).surjective
    exact this
  have hQmem : ∀ q, q ∈ Q ↔ ∃ r ∈ R, q = g * r * g⁻¹ := by
    intro q
    constructor
    · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, by simp [MulAut.conj_apply]⟩
    · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, by simp [MulAut.conj_apply]⟩
  have htuQ : D.t * u ∈ Q := (hQmem _).mpr ⟨D.z, hzR, hgz'.symm⟩
  have hQCt : Q ≤ D.Ct := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := (hQmem q).mp hq
    have hrz : r * D.z = D.z * r := mem_centralizer_singleton_iff.mp (hRC hr).1
    have hru : r * u = u * r := mem_centralizer_singleton_iff.mp (hRC hr).2
    show g * r * g⁻¹ ∈ centralizer ({D.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have ht : D.t = g * (D.z * u) * g⁻¹ := by
      calc D.t = g * (g⁻¹ * D.t * g) * g⁻¹ := by group
        _ = g * (D.z * u) * g⁻¹ := by rw [hgt]
    have hrzu : r * (D.z * u) = (D.z * u) * r := by
      calc r * (D.z * u) = (r * D.z) * u := by group
        _ = (D.z * r) * u := by rw [hrz]
        _ = D.z * (r * u) := by group
        _ = D.z * (u * r) := by rw [hru]
        _ = (D.z * u) * r := by group
    rw [ht]
    calc g * r * g⁻¹ * (g * (D.z * u) * g⁻¹) = g * (r * (D.z * u)) * g⁻¹ := by group
      _ = g * ((D.z * u) * r) * g⁻¹ := by rw [hrzu]
      _ = g * (D.z * u) * g⁻¹ * (g * r * g⁻¹) := by group
  have hQA : ∀ q ∈ Q, ∀ a ∈ D.Act, q * a = a * q := by
    intro q hq a ha
    obtain ⟨r, hr, rfl⟩ := (hQmem q).mp hq
    have h1 := hRE _ (hAEu a ha) r hr
    calc g * r * g⁻¹ * a = g * (r * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * r) * g⁻¹ := by rw [h1]
      _ = a * (g * r * g⁻¹) := by group
  obtain ⟨T', hQT', hT'Ct, hT'p, hT'max⟩ := exists_maximal_two_subgroup D.Ct Q hQCt hQp
  obtain ⟨c, hc, hT'c⟩ := sylow_conj_of_maximal D.Ct hT.T_le hT.T_p hT.T_max hT'Ct hT'p hT'max
  set Q' : Subgroup G := Q.map (MulAut.conj c⁻¹).toMonoidHom with hQ'
  have hQ'T : Q' ≤ T := by
    rintro _ ⟨q, hq, rfl⟩
    have : q ∈ T.map (MulAut.conj c).toMonoidHom := hT'c ▸ hQT' hq
    obtain ⟨s, hsT, hsq⟩ := this
    have : (MulAut.conj c⁻¹).toMonoidHom q = s := by
      have h2 : c * s * c⁻¹ = q := by simpa [MulAut.conj_apply] using hsq
      rw [← h2]; simp; group
    rw [this]; exact hsT
  have hQ'mem : ∀ q', q' ∈ Q' ↔ ∃ q ∈ Q, q' = c⁻¹ * q * c := by
    intro q'
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, by simp⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, by simp⟩
  have hQ'p : IsPGroup 2 Q' := hQp.map _
  have hQ'card : Nat.card ↥Q' = 2 ^ (D.n - 1) := by
    rw [hQ', Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]; exact hQcard
  have hQ'cyc : IsCyclic ↥Q' := by
    have : IsCyclic ↥(Q.map (MulAut.conj c⁻¹).toMonoidHom) :=
      isCyclic_of_surjective (Subgroup.equivMapOfInjective Q _ (MulAut.conj c⁻¹).injective).toMonoidHom
        (Subgroup.equivMapOfInjective Q _ (MulAut.conj c⁻¹).injective).surjective
    exact this
  have hQ'A : ∀ q' ∈ Q', ∀ a ∈ D.Act, q' * a = a * q' := by
    intro q' hq' a ha
    obtain ⟨q, hq, rfl⟩ := (hQ'mem q').mp hq'
    have hca : c * a * c⁻¹ ∈ D.Act := Act_normal D c hc a ha
    have h1 := hQA q hq _ hca
    calc c⁻¹ * q * c * a = c⁻¹ * (q * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * q) * c := by rw [h1]
      _ = a * (c⁻¹ * q * c) := by group
  set u₁ : G := c⁻¹ * u * c with hu₁
  have hu₁I : u₁ ∈ D.Ict := by
    have := hA.I_normal c⁻¹ (D.Ct.inv_mem hc) u hu.mem_I
    simpa using this
  have htc : D.t * c = c * D.t := (mem_centralizer_singleton_iff.mp hc).symm
  have htu₁Q' : D.t * u₁ ∈ Q' := by
    refine (hQ'mem _).mpr ⟨D.t * u, htuQ, ?_⟩
    have hct : c⁻¹ * D.t * c = D.t := by
      calc c⁻¹ * D.t * c = c⁻¹ * (D.t * c) := by group
        _ = c⁻¹ * (c * D.t) := by rw [htc]
        _ = D.t := by group
    rw [hu₁]
    calc D.t * (c⁻¹ * u * c) = (c⁻¹ * D.t * c) * (c⁻¹ * u * c) := by rw [hct]
      _ = c⁻¹ * (D.t * u) * c := by group
  have hu₁T : u₁ ∈ T := by
    have h1 := hQ'T htu₁Q'
    have : u₁ = D.t⁻¹ * (D.t * u₁) := by group
    rw [this]
    exact T.mul_mem (T.inv_mem (hT.zt_le (Subgroup.mem_sup_right (mem_zpowers _)))) h1
  have hu₁T₁ : u₁ ∈ T₁ := by rw [hT.T₁_eq]; exact ⟨hu₁T, hu₁I⟩
  have hu₁2 : u₁ * u₁ = 1 := by
    calc u₁ * u₁ = c⁻¹ * (u * u) * c := by rw [hu₁]; group
      _ = 1 := by rw [hu2]; group
  have htt := t_mul_t' D hs
  have htne : D.t ≠ 1 := by
    intro h1
    have := hs.syl.t_ord
    rw [h1, orderOf_one] at this
    omega
  have htu₁2 : (D.t * u₁) * (D.t * u₁) = 1 := by
    have hcomm : u₁ * D.t = D.t * u₁ := by
      have hu₁Ct : u₁ ∈ D.Ct := Ict_le_Ct D hs hu₁I
      exact mem_centralizer_singleton_iff.mp hu₁Ct
    calc (D.t * u₁) * (D.t * u₁) = D.t * (u₁ * D.t) * u₁ := by group
      _ = D.t * (D.t * u₁) * u₁ := by rw [hcomm]
      _ = (D.t * D.t) * (u₁ * u₁) := by group
      _ = 1 := by rw [htt, hu₁2]; group
  have htu₁ne : D.t * u₁ ≠ 1 := by
    intro h1
    have : D.t = u₁⁻¹ := by
      calc D.t = (D.t * u₁) * u₁⁻¹ := by group
        _ = u₁⁻¹ := by rw [h1]; group
    have htI : D.t ∈ D.Ict := by rw [this]; exact D.Ict.inv_mem hu₁I
    exact t_not_mem_K D.ext3 hs (Ict_le_K D hs htI)
  obtain ⟨q'g, hq'g⟩ := hQ'cyc.exists_generator
  set q' : G := (q'g : G) with hq'
  have hq'Q' : q' ∈ Q' := q'g.2
  have hq'o : orderOf q' = 2 ^ (D.n - 1) := by
    rw [hq', Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hq'g, hQ'card]
  have hmpos : 1 ≤ D.n - 2 := by omega
  have hq'm : q' ^ (2 ^ (D.n - 2)) = D.t * u₁ := by
    have hmem : D.t * u₁ ∈ zpowers q' := by
      have h1 := hq'g ⟨D.t * u₁, htu₁Q'⟩
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h1
      exact mem_zpowers_iff.mpr ⟨j, congrArg Subtype.val hj⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
    set h : G := q' ^ (2 ^ (D.n - 2)) with hh
    have hh2 : orderOf h = 2 := by
      have h1 : h * h = 1 := by
        rw [hh, ← pow_add, ← two_mul, ← pow_succ']
        have : D.n - 2 + 1 = D.n - 1 := by omega
        rw [this, ← hq'o]; exact pow_orderOf_eq_one q'
      refine orderOf_eq_prime (by rw [pow_two]; exact h1) ?_
      intro h1
      have : orderOf q' ∣ 2 ^ (D.n - 2) := orderOf_dvd_of_pow_eq_one h1
      rw [hq'o] at this
      have := Nat.le_of_dvd (by positivity) this
      have h2 : 2 ^ (D.n - 2) < 2 ^ (D.n - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hj2 : (q' ^ j) ^ 2 = 1 := by
      rw [hj, pow_two]; exact htu₁2
    have h3 : 2 ^ (D.n - 1) ∣ j * 2 := by
      have : q' ^ (j * 2) = 1 := by rw [zpow_mul, zpow_two, ← pow_two]; exact hj2
      exact (orderOf_dvd_iff_zpow_eq_one.mpr this |> fun h => by
        rw [hq'o] at h; exact_mod_cast h)
    have h4 : (2 ^ (D.n - 2) : ℤ) ∣ j := by
      have : ((2 : ℤ) ^ (D.n - 1)) ∣ j * 2 := by exact_mod_cast h3
      have e : (2 : ℤ) ^ (D.n - 1) = 2 ^ (D.n - 2) * 2 := by
        have : D.n - 1 = (D.n - 2) + 1 := by omega
        rw [this, pow_succ]
      rw [e, mul_comm j 2, mul_comm (2 ^ (D.n - 2) : ℤ) 2] at this
      exact (Int.dvd_of_mul_dvd_mul_left (by norm_num) this)
    obtain ⟨k, hk⟩ := h4
    have hjh : q' ^ j = h ^ k := by
      rw [hk, zpow_mul, hh]; norm_cast
    rcases zpow_cases_two' hh2 k with h5 | h5
    · exfalso
      apply htu₁ne
      rw [← hj, hjh, h5]
    · rw [← hj, hjh, h5]
  have hq'T : q' ∈ T := hQ'T hq'Q'
  have hq'notin : q' ∉ T₀ ⊔ T₁ := by
    intro hmem
    obtain ⟨t₀, ht₀, t₁, ht₁, hq'e⟩ := mem_sup_of_commute hT.T₀_T₁ hmem
    have h1 := dihedral_pow_exp hn3 T₀ hT.T₀_dih t₀ ht₀
    have h2 := dihedral_pow_exp hn3 T₁ hT.T₁_dih t₁ ht₁
    have : q' ^ (2 ^ (D.n - 2)) = 1 := by
      rw [hq'e, (show Commute t₀ t₁ from hT.T₀_T₁ t₀ ht₀ t₁ ht₁).mul_pow, h1, h2, mul_one]
    rw [hq'm] at this
    exact htu₁ne this
  have hTeq : T = (T₀ ⊔ T₁) ⊔ zpowers y := hT.T_eq
  have hq'T' : q' ∈ (T₀ ⊔ T₁) ⊔ zpowers y := hTeq ▸ hq'T
  obtain ⟨w₁, hw₁, k, hk, hq'wk⟩ := sup_decomp_of_le_normalizer hT.y_norm_T₀T₁ hq'T'
  have hy2 : orderOf y = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact hT.y_sq) ?_
    intro h1
    apply hT.y_not_mem hs
    rw [h1]; exact one_mem _
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hk
  have hq'wy : q' = w₁ * y := by
    rcases zpow_cases_two' hy2 j with h | h
    · exfalso
      apply hq'notin
      rw [hq'wk, h, mul_one]; exact hw₁
    · rw [hq'wk, h]
  obtain ⟨t₀, ht₀, t₁, ht₁, hw₁e⟩ := mem_sup_of_commute hT.T₀_T₁ hw₁
  have ht₁I : t₁ ∈ D.Ict := by
    have : t₁ ∈ T ⊓ D.Ict := hT.T₁_eq ▸ ht₁
    exact this.2
  set w : G := t₀ * y with hw
  have hq't : q' = t₁ * w := by
    rw [hq'wy, hw₁e, hw]
    have hc : t₀ * t₁ = t₁ * t₀ := hT.T₀_T₁ t₀ ht₀ t₁ ht₁
    calc t₀ * t₁ * y = (t₁ * t₀) * y := by rw [hc]
      _ = t₁ * (t₀ * y) := by group
  have hwA : ∀ a ∈ D.Act, a * w = w * a := by
    intro a ha
    have hw' : w = t₁⁻¹ * q' := by rw [hq't]; group
    have h1 : a * t₁⁻¹ = t₁⁻¹ * a := by
      have := hA.AI_comm a ha t₁ ht₁I
      calc a * t₁⁻¹ = t₁⁻¹ * (t₁ * a) * t₁⁻¹ := by group
        _ = t₁⁻¹ * (a * t₁) * t₁⁻¹ := by rw [this]
        _ = t₁⁻¹ * a := by group
    rw [hw']
    calc a * (t₁⁻¹ * q') = (a * t₁⁻¹) * q' := by group
      _ = (t₁⁻¹ * a) * q' := by rw [h1]
      _ = t₁⁻¹ * (a * q') := by group
      _ = t₁⁻¹ * (q' * a) := by rw [(hQ'A q' hq'Q' a ha).symm]
      _ = t₁⁻¹ * q' * a := by group
  have hwT : w ∈ T := T.mul_mem (T₀_le_T D hT ht₀) hT.y_mem
  have hwY : w ∈ T₀ ⊔ zpowers y :=
    Subgroup.mul_mem_sup ht₀ (mem_zpowers y)
  have hwm : w ^ (2 ^ (D.n - 2)) = D.t := by
    obtain ⟨s, hs₁, hsw⟩ := pow_mul_mem_aux T₁ T hT.T₁_norm ht₁ hwT (2 ^ (D.n - 2))
    have h1 : s * w ^ (2 ^ (D.n - 2)) = D.t * u₁ := by rw [← hsw, ← hq't, hq'm]
    have hscomm : s * D.t = D.t * s := mem_centralizer_singleton_iff.mp
      (Ict_le_Ct D hs (by have : s ∈ T ⊓ D.Ict := hT.T₁_eq ▸ hs₁; exact this.2))
    have h2 : D.t⁻¹ * w ^ (2 ^ (D.n - 2)) = s⁻¹ * u₁ := by
      have h3 : w ^ (2 ^ (D.n - 2)) = s⁻¹ * (D.t * u₁) := by
        calc w ^ (2 ^ (D.n - 2)) = s⁻¹ * (s * w ^ (2 ^ (D.n - 2))) := by group
          _ = s⁻¹ * (D.t * u₁) := by rw [h1]
      rw [h3]
      calc D.t⁻¹ * (s⁻¹ * (D.t * u₁)) = (D.t⁻¹ * s⁻¹ * D.t) * u₁ := by group
        _ = s⁻¹ * u₁ := by
          have : D.t⁻¹ * s⁻¹ * D.t = s⁻¹ := by
            have h5 : s⁻¹ * D.t = D.t * s⁻¹ := by
              have := (show Commute s D.t from hscomm).inv_left.eq
              exact this
            calc D.t⁻¹ * s⁻¹ * D.t = D.t⁻¹ * (s⁻¹ * D.t) := by group
              _ = D.t⁻¹ * (D.t * s⁻¹) := by rw [h5]
              _ = s⁻¹ := by group
          rw [this]
    have hY1 : D.t⁻¹ * w ^ (2 ^ (D.n - 2)) ∈ T₀ ⊔ zpowers y :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hT.t_T₀))
        (Subgroup.pow_mem _ hwY _)
    have hT1 : D.t⁻¹ * w ^ (2 ^ (D.n - 2)) ∈ T₁ := by
      rw [h2]; exact T₁.mul_mem (T₁.inv_mem hs₁) hu₁T₁
    have hbot : D.t⁻¹ * w ^ (2 ^ (D.n - 2)) ∈ (T₀ ⊔ zpowers y) ⊓ T₁ := ⟨hY1, hT1⟩
    rw [hT.Y_inf_T₁ hs, Subgroup.mem_bot] at hbot
    calc w ^ (2 ^ (D.n - 2)) = D.t * (D.t⁻¹ * w ^ (2 ^ (D.n - 2))) := by group
      _ = D.t := by rw [hbot, mul_one]
  have hwo : orderOf w = 2 ^ (D.n - 1) := by
    have hp : ¬ w ^ (2 ^ (D.n - 2)) = 1 := by rw [hwm]; exact htne
    have hp2 : w ^ (2 ^ (D.n - 2 + 1)) = 1 := by
      rw [pow_succ, pow_mul, hwm, pow_two]; exact htt
    have := orderOf_eq_prime_pow (p := 2) hp hp2
    have e : D.n - 2 + 1 = D.n - 1 := by omega
    rw [e] at this
    exact this
  have hzp : zpowers x = zpowers w :=
    dihedral_cyclic_index_two_unique hn3 (T₀ ⊔ zpowers y) hT.T₀y_dih x w hxY hwY hxo hwo
  have hxw : x ∈ zpowers w := hzp ▸ mem_zpowers x
  intro a ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hxw
  exact ((show Commute a w from hwA a ha).zpow_right j).eq

end CtAx

end CFSG.GH74.GLS.SP.Local
