module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi23TwistDefs
public import CFSG.Sporadic.FischerOddCore.Fi23LocalComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Sporadic.FischerOddCore

section General

variable {G : Type} [Group G]

private theorem map_conj_inv_le {h u : G} {D : Subgroup G}
    (hD : D ≤ Subgroup.centralizer ({h * u * h⁻¹} : Set G)) :
    D.map (MulAut.conj h⁻¹).toMonoidHom ≤ Subgroup.centralizer ({u} : Set G) := by
  have := map_conj_le_centralizer_singleton h⁻¹ hD
  rwa [show h⁻¹ * (h * u * h⁻¹) * h⁻¹⁻¹ = u by group] at this

private theorem card_map_conj (g : G) (D : Subgroup G) :
    Nat.card (D.map (MulAut.conj g).toMonoidHom) = Nat.card D :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

private theorem mem_centralizer_of_conj {x u : G} (h : x * u * x⁻¹ = u) :
    x ∈ Subgroup.centralizer ({u} : Set G) :=
  (Subgroup.mem_centralizer_singleton_iff (G := G)).2 (mul_inv_eq_iff_eq_mul.1 h)

end General

theorem le_centralizer_d_d1
    {D : Subgroup J} (hD : IsElemAbelian 3 D)
    (h : D ≤ Subgroup.centralizer ({d * d1} : Set J)) :
    D ≤ Subgroup.centralizer ({d} : Set J) ⊓ Subgroup.centralizer ({d1} : Set J) := by
  intro c hc
  have hcc : c * (d * d1) = d * d1 * c := (Subgroup.mem_centralizer_singleton_iff (G := J)).1 (h hc)
  have e1 : c * (d * d1) * c⁻¹ = d * d1 := by rw [hcc, mul_inv_cancel_right]
  have hc3 : c ^ 3 ^ 1 = 1 := by simpa using hD.2 c hc
  have key : c * d1 * c⁻¹ = c * d * c⁻¹ * (d * d1) := by
    rw [← e1, show c * d * c⁻¹ * (c * (d * d1) * c⁻¹) = c * (d * d) * d1 * c⁻¹ by group, d_sq,
      mul_one]
  have hcd : c * d * c⁻¹ = d := by
    rcases fi23_pair_unique c hcc with h1 | h1
    · exact h1
    · exfalso
      refine not_swap hc3 d1_mem_localClass.2.1.symm h1 ?_
      rw [key, h1, ← mul_assoc, d1_commute, mul_assoc, ← pow_two, d1_sq, mul_one]
  have hcd1 : c * d1 * c⁻¹ = d1 := by rw [key, hcd, ← mul_assoc, d_sq, one_mul]
  exact Subgroup.mem_inf.2 ⟨mem_centralizer_of_conj hcd, mem_centralizer_of_conj hcd1⟩


theorem twoA_transfer_d (h22 : I1017FiTwoTwoTwist) {E T : Subgroup J} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 4 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set J)) (hEd : E ≤ Cd) (hTd : T ≤ Cd) :
    ∀ e ∈ E, ∀ t ∈ T, e * t = t * e := by
  obtain ⟨b⟩ : Nonempty (CFSG.Blueprint.NativeSporadic.Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic .Fi22).Group) := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have hinj : Function.Injective (fi23Kappa.comp (Subgroup.inclusion hEd)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [MonoidHom.comp_apply] at hx
    rcases fi23Kappa_eq_one hx with h | h <;> rw [Subgroup.coe_inclusion] at h
    · exact Subtype.ext h
    · exfalso
      have h3 : d ^ 3 = 1 := hE.2 d (h ▸ x.2)
      rw [pow_succ, d_sq', one_mul] at h3
      exact d_ne_one h3
  have hcardE : Nat.card ((E.subgroupOf Cd).map fi23Kappa) = Nat.card E := by
    rw [← Subgroup.inclusion_range hEd, ← MonoidHom.range_comp]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hET' : E.subgroupOf Cd ≤
      Subgroup.normalizer ((T.subgroupOf Cd : Subgroup Cd) : Set Cd) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := (Subgroup.mem_normalizer_iff.1 (hET (Subgroup.mem_subgroupOf.1 hx))) (y : J)
    simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      using this
  have hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs ↥CFSG.Sporadic.Fi22.J (S8.sporIs .Fi22) :=
    ⟨.sporadic .Fi22, rfl, ⟨CFSG.Monster.B.Fischer.fi22MatEquiv.symm.trans b⟩⟩
  have hT' : IsPGroup 2 (T.subgroupOf Cd) := by
    rw [← Subgroup.comap_subtype]
    exact hT.comap_subtype
  have key := h22 _ hcat _ (isElemAbelian_map' fi23Kappa (isElemAbelian_subgroupOf hE Cd))
    (by rw [hcardE]; exact hcard) _ (hT'.map fi23Kappa)
    ((Subgroup.map_mono (f := fi23Kappa) hET').trans (Subgroup.le_normalizer_map fi23Kappa))
  intro e he t ht
  obtain ⟨a, rfl⟩ : ∃ a : Cd, (a : J) = e := ⟨⟨e, hEd he⟩, rfl⟩
  obtain ⟨c, rfl⟩ : ∃ c : Cd, (c : J) = t := ⟨⟨t, hTd ht⟩, rfl⟩
  have hac := key (fi23Kappa a) ⟨a, Subgroup.mem_subgroupOf.2 he, rfl⟩ (fi23Kappa c)
    ⟨c, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  have hk : fi23Kappa (a * c * a⁻¹ * c⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hac]
    group
  have he3 : (a : J) ^ 3 = 1 := hE.2 _ he
  rcases fi23Kappa_eq_one hk with h | h <;> simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
  · calc (a : J) * c = a * c * (a : J)⁻¹ * (c : J)⁻¹ * (c * a) := by group
      _ = c * a := by rw [h, one_mul]
  · exfalso
    have h1 : (c : J) * (a : J)⁻¹ * (c : J)⁻¹ = (a : J)⁻¹ * d := by
      rw [← h]
      group
    have h2 : ((c : J) * (a : J)⁻¹ * (c : J)⁻¹) ^ 3 = 1 := by
      rw [conj_pow, inv_pow, he3, inv_one, mul_one, mul_inv_cancel]
    have had : (a : J) * d = d * (a : J) := mem_Cd.1 (hEd he)
    have hdi : d * (a : J)⁻¹ = (a : J)⁻¹ * d := by
      calc d * (a : J)⁻¹ = (a : J)⁻¹ * ((a : J) * d) * (a : J)⁻¹ := by group
        _ = (a : J)⁻¹ * (d * (a : J)) * (a : J)⁻¹ := by rw [had]
        _ = (a : J)⁻¹ * d := by group
    have h3 : ((a : J)⁻¹ * d) ^ 3 = ((a : J) ^ 3)⁻¹ * (d * d * d) := by
      calc ((a : J)⁻¹ * d) ^ 3 = (a : J)⁻¹ * (d * (a : J)⁻¹) * (d * (a : J)⁻¹) * d := by
            rw [pow_succ, pow_succ, pow_one]; group
        _ = (a : J)⁻¹ * ((a : J)⁻¹ * d) * ((a : J)⁻¹ * d) * d := by rw [hdi]
        _ = (a : J)⁻¹ * (a : J)⁻¹ * (d * (a : J)⁻¹) * d * d := by group
        _ = (a : J)⁻¹ * (a : J)⁻¹ * ((a : J)⁻¹ * d) * d * d := by rw [hdi]
        _ = ((a : J) ^ 3)⁻¹ * (d * d * d) := by rw [pow_succ, pow_succ, pow_one]; group
    rw [h1, h3, he3, inv_one, one_mul, d_sq, one_mul] at h2
    exact d_ne_one h2

theorem twoA_transfer (h22 : I1017FiTwoTwoTwist) {E T : Subgroup J} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 4 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set J)) {z : J} (hz : z ∈ D23)
    (hEz : E ≤ Subgroup.centralizer ({z} : Set J))
    (hTz : T ≤ Subgroup.centralizer ({z} : Set J)) : ∀ e ∈ E, ∀ t ∈ T, e * t = t * e := by
  obtain ⟨h, rfl⟩ := isConj_iff.1 (show IsConj d z from hz)
  have key := twoA_transfer_d h22 (isElemAbelian_map' (MulAut.conj h⁻¹).toMonoidHom hE)
    (by rw [card_map_conj]; exact hcard) (hT.map (MulAut.conj h⁻¹).toMonoidHom)
    ((Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _)) (map_conj_inv_le hEz)
    (map_conj_inv_le hTz)
  intro e he t ht
  have := key _ ⟨e, he, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [← map_mul, ← map_mul] at this
  exact (MulAut.conj h⁻¹).injective this

theorem twoB_transfer_d
    (h22 : I1017FiTwoTwoTwist) {E T : Subgroup J} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 4 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set J))
    (hEz : E ≤ Subgroup.centralizer ({d * d1} : Set J))
    (hTz : T ≤ Subgroup.centralizer ({d * d1} : Set J)) : ∀ e ∈ E, ∀ t ∈ T, e * t = t * e := by
  have hE2 := le_centralizer_d_d1 hE hEz
  have hEd : E ≤ Cd := fun x hx => (Subgroup.mem_inf.1 (hE2 hx)).1
  have hET2 : E ≤ Subgroup.normalizer ((T ⊓ Cd : Subgroup J) : Set J) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (hET hx) y
    have hxd : x ∈ Cd := hEd hx
    constructor
    · rintro ⟨hyT, hyd⟩
      exact ⟨h1.1 hyT, Cd.mul_mem (Cd.mul_mem hxd hyd) (Cd.inv_mem hxd)⟩
    · rintro ⟨hyT, hyd⟩
      refine ⟨h1.2 hyT, ?_⟩
      rw [show y = x⁻¹ * (x * y * x⁻¹) * x by group]
      exact Cd.mul_mem (Cd.mul_mem (Cd.inv_mem hxd) hyd) hxd
  have key := twoA_transfer_d h22 hE hcard (hT.to_le inf_le_left) hET2 hEd inf_le_right
  intro e he s hs
  by_cases hsd : s ∈ Cd
  · exact key e he s ⟨hs, hsd⟩
  have he3 : e ^ 3 = 1 := hE.2 e he
  have hed : e * d * e⁻¹ = d := by rw [mem_Cd.1 (hEd he), mul_inv_cancel_right]
  have hed1 : e⁻¹ * d1 * e = d1 := by
    have h1 := (Subgroup.mem_centralizer_singleton_iff (G := J)).1 (Subgroup.mem_inf.1 (hE2 he)).2
    calc e⁻¹ * d1 * e = e⁻¹ * (e * d1) := by rw [h1, mul_assoc]
      _ = d1 := by group
  have hsz : s * (d * d1) = d * d1 * s :=
    (Subgroup.mem_centralizer_singleton_iff (G := J)).1 (hTz hs)
  have hs1 : s * d * s⁻¹ = d1 := by
    rcases fi23_pair_unique s hsz with h | h
    · refine (hsd (mem_Cd.2 ?_)).elim
      calc s * d = s * d * s⁻¹ * s := by group
        _ = d * s := by rw [h]
    · exact h
  have hs2 : s * d1 * s⁻¹ = d := by
    have h1 : s * d * s⁻¹ * (s * d1 * s⁻¹) = d * d1 := by
      calc s * d * s⁻¹ * (s * d1 * s⁻¹) = s * (d * d1) * s⁻¹ := by group
        _ = d * d1 := by rw [hsz, mul_inv_cancel_right]
    rw [hs1] at h1
    calc s * d1 * s⁻¹ = d1⁻¹ * (d1 * (s * d1 * s⁻¹)) := by group
      _ = d := by rw [h1, ← d1_commute, inv_mul_cancel_left]
  have hsi : s⁻¹ * d * s = d1 := by
    calc s⁻¹ * d * s = s⁻¹ * (s * d1 * s⁻¹) * s := by rw [hs2]
      _ = d1 := by group
  set c := e * s * e⁻¹ * s⁻¹ with hc
  have hcT : c ∈ T := T.mul_mem ((Subgroup.mem_normalizer_iff.1 (hET he) s).1 hs) (T.inv_mem hs)
  have hcd : c * d * c⁻¹ = d := by
    calc c * d * c⁻¹ = e * s * (e⁻¹ * (s⁻¹ * d * s) * e) * s⁻¹ * e⁻¹ := by rw [hc]; group
      _ = e * (s * d1 * s⁻¹) * e⁻¹ := by rw [hsi, hed1]; group
      _ = d := by rw [hs2, hed]
  have hcC : c * d = d * c := by
    calc c * d = c * d * c⁻¹ * c := by group
      _ = d * c := by rw [hcd]
  have hce : e * c * e⁻¹ = c := by rw [key e he c ⟨hcT, mem_Cd.2 hcC⟩, mul_inv_cancel_right]
  have hes : e * s * e⁻¹ = c * s := by rw [hc]; group
  have hB : e * (c * s) * e⁻¹ = c * (c * s) := by
    calc e * (c * s) * e⁻¹ = (e * c * e⁻¹) * (e * s * e⁻¹) := by group
      _ = c * (c * s) := by rw [hce, hes]
  have hC : e * (c * (c * s)) * e⁻¹ = c * (c * (c * s)) := by
    calc e * (c * (c * s)) * e⁻¹ = (e * c * e⁻¹) * (e * (c * s) * e⁻¹) := by group
      _ = c * (c * (c * s)) := by rw [hce, hB]
  have hc3 : c ^ 3 ^ 1 = 1 := by
    have h1 : e ^ 3 * s * (e ^ 3)⁻¹ = e * (e * (e * s * e⁻¹) * e⁻¹) * e⁻¹ := by
      rw [pow_succ, pow_succ, pow_one]; group
    rw [hes, hB, hC, he3, one_mul, inv_one, mul_one] at h1
    have h2 : c * (c * (c * s)) = c ^ 3 * s := by rw [pow_succ, pow_succ, pow_one]; group
    rw [pow_one]
    exact mul_right_cancel ((h2.symm.trans h1.symm).trans (one_mul s).symm)
  obtain ⟨k, hk⟩ := hT ⟨c, hcT⟩
  have hc2 : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hc1 := eq_one_of_pow_two_pow_p Nat.prime_three (by norm_num) hc3 hc2
  rw [hc1, one_mul] at hes
  calc e * s = e * s * e⁻¹ * e := by group
    _ = s * e := by rw [hes]

theorem twoB_transfer
    (h22 : I1017FiTwoTwoTwist) {E T : Subgroup J} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 4 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set J)) {z : J} (hz : IsConj (d * d1) z)
    (hEz : E ≤ Subgroup.centralizer ({z} : Set J))
    (hTz : T ≤ Subgroup.centralizer ({z} : Set J)) : ∀ e ∈ E, ∀ t ∈ T, e * t = t * e := by
  obtain ⟨h, rfl⟩ := isConj_iff.1 hz
  have key := twoB_transfer_d h22 (isElemAbelian_map' (MulAut.conj h⁻¹).toMonoidHom hE)
    (by rw [card_map_conj]; exact hcard) (hT.map (MulAut.conj h⁻¹).toMonoidHom)
    ((Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _)) (map_conj_inv_le hEz)
    (map_conj_inv_le hTz)
  intro e he t ht
  have := key _ ⟨e, he, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [← map_mul, ← map_mul] at this
  exact (MulAut.conj h⁻¹).injective this

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist
