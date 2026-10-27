module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step47Code
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cz2
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Sylow

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup Q47 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

namespace VCode

variable {G : Type} [Group G] {Q : Subgroup G} {z : G}

@[expose] noncomputable def img (c : VCode Q z) (hs : Std Q z) (K : Subgroup G) :
    Subgroup (Equiv.Perm (Fin 64)) :=
  (K.subgroupOf (normalizer (Q : Set G))).map (c.rho hs)

variable {c : VCode Q z} {hs : Std Q z}

theorem mem_img_of_mem {K : Subgroup G} {k : G} (hk : k ∈ K)
    (hkN : k ∈ normalizer (Q : Set G)) : c.rho hs ⟨k, hkN⟩ ∈ c.img hs K :=
  ⟨⟨k, hkN⟩, hk, rfl⟩

theorem img_mono {K L : Subgroup G} (h : K ≤ L) : c.img hs K ≤ c.img hs L :=
  map_mono fun _ hx => h hx

theorem img_sup {K L : Subgroup G} (hK : K ≤ normalizer (Q : Set G))
    (hL : L ≤ normalizer (Q : Set G)) : c.img hs (K ⊔ L) = c.img hs K ⊔ c.img hs L := by
  rw [img, img, img, subgroupOf_sup hK hL, Subgroup.map_sup]

theorem img_le_oV (K : Subgroup G) : c.img hs K ≤ oV := by
  rintro _ ⟨n, -, rfl⟩
  exact rho_mem_oV hs n

theorem img_le_normalizer {K L : Subgroup G} (hKL : K ≤ normalizer (L : Set G)) :
    c.img hs K ≤ normalizer (c.img hs L : Set (Equiv.Perm (Fin 64))) := by
  rintro _ ⟨k, hk, rfl⟩
  refine mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  exact ⟨k * l * k⁻¹, (mem_normalizer_iff.mp (hKL hk) l).mp hl, rfl⟩

theorem range_comp_inclusion {K : Subgroup G} (hK : K ≤ normalizer (Q : Set G)) :
    ((c.rho hs).comp (inclusion hK)).range = c.img hs K := by
  rw [MonoidHom.range_comp, inclusion_range]
  rfl

theorem card_img [Finite G] (hnd : nondegCheck = true)
    (hcent : centralizer (Q : Set G) ≤ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)))
    {K : Subgroup G} (hK : K ≤ normalizer (Q : Set G)) :
    Nat.card K =
      Nat.card (K ⊓ (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))) : Subgroup G) *
        Nat.card (c.img hs K) := by
  have h := card_eq_card_inf_ker_mul_card_map (c.rho hs) (K.subgroupOf (normalizer (Q : Set G)))
  have e : K.subgroupOf (normalizer (Q : Set G)) ⊓ (c.rho hs).ker =
      (K ⊓ (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)))).subgroupOf
        (normalizer (Q : Set G)) := by
    rw [ker_rho hs hnd hcent]
    ext x
    exact Iff.rfl
  rw [e, Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hK)).toEquiv] at h
  exact h

section Model

variable {n : ℕ} {Xm : Subgroup (Equiv.Perm (Fin n))} {reps : List (Array ℕ)} {zg : Array ℕ}
  {f : ↥Xm →* ↥(normalizer (Q : Set G))}

theorem img_trS (K : Subgroup (Equiv.Perm (Fin n))) :
    c.img hs (trS ((normalizer (Q : Set G)).subtype.comp f) K) =
      (K.subgroupOf Xm).map ((c.rho hs).comp f) := by
  rw [img, ← map_map]
  congr 1
  ext y
  rw [mem_subgroupOf, mem_trS, mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, Subtype.ext hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

variable (hrepX : ∀ v, repV n reps v ∈ Xm)
  (hrep : ∀ v, c.rep v = (f ⟨repV n reps v, hrepX v⟩ : G)) (hzX : permOfArr n zg ∈ Xm)
  (hz : z = (f ⟨permOfArr n zg, hzX⟩ : G))
include hrep hz

theorem rho_eq_of_actsBy {g : Equiv.Perm (Fin n)} (hg : g ∈ Xm) {d : Equiv.Perm (Fin 64)}
    (h : ActsBy n reps zg g d) : c.rho hs (f ⟨g, hg⟩) = d := by
  refine Equiv.ext fun v => ?_
  show c.act (f ⟨g, hg⟩) v = d v
  refine act_eq hs ?_
  have e1 : ∀ (a : Equiv.Perm (Fin n)) (ha : a ∈ Xm), g * repV n reps v * g⁻¹ = a →
      (f ⟨g, hg⟩ : G) * c.rep v * (f ⟨g, hg⟩ : G)⁻¹ = (f ⟨a, ha⟩ : G) := by
    intro a ha e
    have e' : (⟨g, hg⟩ : ↥Xm) * ⟨repV n reps v, hrepX v⟩ * (⟨g, hg⟩ : ↥Xm)⁻¹ = ⟨a, ha⟩ :=
      Subtype.ext e
    rw [hrep v, ← e', map_mul, map_mul, map_inv]
    rfl
  rcases h v with h1 | h1
  · exact Or.inl ((e1 _ _ h1).trans (hrep _).symm)
  · right
    rw [e1 _ (Xm.mul_mem (hrepX _) hzX) h1, hrep (d v), hz]
    have e2 : (⟨repV n reps (d v) * permOfArr n zg, Xm.mul_mem (hrepX _) hzX⟩ : ↥Xm) =
        ⟨repV n reps (d v), hrepX _⟩ * ⟨permOfArr n zg, hzX⟩ := rfl
    rw [e2, map_mul]
    rfl

theorem map_grpN_eq {gs ds : List (Array ℕ)} (hgX : grpN n gs ≤ Xm)
    (hact : gs.length = ds.length ∧ ∀ k < gs.length, validA 64 ds[k]! = true ∧
      ActsBy n reps zg (permOfArr n gs[k]!) (permOfArr 64 ds[k]!)) :
    ((grpN n gs).subgroupOf Xm).map ((c.rho hs).comp f) = grpN 64 ds := by
  obtain ⟨hlen, hk⟩ := hact
  have hmemk : ∀ k < gs.length, gs[k]! ∈ gs := fun k hk' => by
    rw [getElem!_pos gs k hk']
    exact List.getElem_mem _
  have himg : ∀ k (hk' : k < gs.length),
      (c.rho hs).comp f ⟨permOfArr n gs[k]!, hgX (gen_mem_grpN (hmemk k hk'))⟩ =
        permOfArr 64 ds[k]! :=
    fun k hk' => rho_eq_of_actsBy (hs := hs) hrepX hrep hzX hz _ (hk k hk').2
  have hds : ∀ k < gs.length, ds[k]! ∈ ds := fun k hk' => by
    rw [getElem!_pos ds k (by omega)]
    exact List.getElem_mem _
  refine le_antisymm ?_ ?_
  · rw [map_le_iff_le_comap]
    intro x hx
    have key : ∀ y (hy : y ∈ grpN n gs), (c.rho hs).comp f ⟨y, hgX hy⟩ ∈ grpN 64 ds := by
      intro y hy
      change y ∈ closure (permsA n gs.toArray) at hy
      induction hy using Subgroup.closure_induction with
      | mem y hy' =>
        rw [mem_permsA_iff] at hy'
        obtain ⟨t, ht, rfl⟩ := hy'
        obtain ⟨k, hk', hkt⟩ := List.getElem_of_mem ht
        have ht' : gs[k]! = t := by rw [getElem!_pos gs k hk']; exact hkt
        subst ht'
        rw [himg k hk']
        exact gen_mem_grpN (hds k hk')
      | one =>
        rw [show (⟨1, hgX (one_mem _)⟩ : ↥Xm) = 1 from rfl, map_one]
        exact one_mem _
      | mul a b ha hb iha ihb =>
        rw [show (⟨a * b, hgX (mul_mem ha hb)⟩ : ↥Xm) = ⟨a, hgX ha⟩ * ⟨b, hgX hb⟩ from rfl,
          map_mul]
        exact mul_mem iha ihb
      | inv a ha iha =>
        rw [show (⟨a⁻¹, hgX (inv_mem ha)⟩ : ↥Xm) = (⟨a, hgX ha⟩)⁻¹ from rfl, map_inv]
        exact inv_mem iha
    exact key x hx
  · rw [grpN, closure_le]
    intro d hd
    rw [mem_permsA_iff] at hd
    obtain ⟨t, ht, rfl⟩ := hd
    obtain ⟨k, hk', hkt⟩ := List.getElem_of_mem ht
    have hkg : k < gs.length := by omega
    refine ⟨⟨permOfArr n gs[k]!, hgX (gen_mem_grpN (hmemk k hkg))⟩,
      gen_mem_grpN (hmemk k hkg), ?_⟩
    rw [himg k hkg, getElem!_pos ds k hk', hkt]

end Model

theorem img_iX_eq [Finite G] (hnd : nondegCheck = true)
    (hcent : centralizer (Q : Set G) ≤ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)))
    {I X P : Subgroup G} {Xb D K0 K1 : List (Array ℕ)}
    (hQI : Q ≤ I) (hIN : I ≤ normalizer (Q : Set G)) (hIX : I ≤ normalizer (X : Set G))
    (hcard : Nat.card I = 3072) (h3 : ∀ c ∈ I, c ∈ centralizer (Q : Set G) → orderOf c ≠ 3)
    (hPI : P ≤ I) (hP : c.img hs P = grpN 64 D) (hX : c.img hs X = grpN 64 Xb)
    (hcand : ∀ K : Subgroup (Equiv.Perm (Fin 64)), K ≤ oV → Nat.card K = 24 → grpN 64 D ≤ K →
      K ≤ normalizer (grpN 64 Xb : Set (Equiv.Perm (Fin 64))) →
        K = grpN 64 K0 ∨ K = grpN 64 K1) :
    c.img hs I = grpN 64 K0 ∨ c.img hs I = grpN 64 K1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := AS76b.oddCoreIn (normalizer (Q : Set G)) with hOdef
  refine hcand _ (img_le_oV I) ?_ (hP ▸ img_mono hPI) (hX ▸ img_le_normalizer hIX)
  have hIO : I ⊓ O = ⊥ := by
    have hodd : Odd (Nat.card (I ⊓ O : Subgroup G)) :=
      (AS76b.odd_card_oddCoreIn _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    have hdvd : Nat.card (I ⊓ O : Subgroup G) ∣ 3 * 2 ^ 10 := by
      rw [show 3 * 2 ^ 10 = Nat.card I by rw [hcard]; norm_num]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h3' : Nat.card (I ⊓ O : Subgroup G) ∣ 3 :=
      (Nat.Coprime.pow_right 10 (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_right hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 h3' with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := (I ⊓ O : Subgroup G)) 3
        (by rw [h1])
      have hw3 : orderOf (w : G) = 3 := by rwa [Subgroup.orderOf_coe]
      exact h3 w (mem_inf.mp w.2).1 (VCode.oddCoreIn_le_centralizer hs (mem_inf.mp w.2).2) hw3
  have hinf : I ⊓ (Q ⊔ O) = Q := by
    refine le_antisymm (fun x hx => ?_) (le_inf hQI le_sup_left)
    have hQO : Q ≤ normalizer (O : Set G) :=
      le_normalizer.trans (AS76b.le_normalizer_oddCoreIn (normalizer (Q : Set G)))
    have hx2 : x ∈ ((Q ⊔ O : Subgroup G) : Set G) := hx.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Q O hQO] at hx2
    obtain ⟨q, hq, o, ho, rfl⟩ := hx2
    show q * o ∈ Q
    have hoI : o ∈ I := by
      have := I.mul_mem (I.inv_mem (hQI hq)) hx.1
      rwa [inv_mul_cancel_left] at this
    have ho1 : o ∈ I ⊓ O := ⟨hoI, ho⟩
    rw [hIO, mem_bot] at ho1
    rw [ho1, mul_one]
    exact hq
  have h := card_img (c := c) (hs := hs) hnd hcent hIN
  rw [hinf, hcard, hs.card] at h
  omega

end VCode

end CFSG.ComponentClassification.AS81
