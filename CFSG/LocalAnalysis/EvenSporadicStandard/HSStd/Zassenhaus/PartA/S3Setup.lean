module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Open

section OddCore

theorem s3_odd_fusionOddCore (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (fusionOddCore H)) := by
  obtain ⟨core, ⟨hn, hodd⟩, hmax⟩ :=
    CFSG.OrderReductions.OddCore.exists_greatest_odd_normal (group := H)
  have : fusionOddCore H = core := by
    refine le_antisymm (sSup_le fun N hN => hmax N ⟨hN.1, hN.2⟩) (le_sSup ⟨hn, hodd⟩)
  rw [this]
  exact hodd

theorem s3_eq_one_of_sq_mem_oddCore {H : Type*} [Group H] [Finite H] {g : H}
    (hg : g ∈ fusionOddCore H) (h : g * g = 1) : g = 1 := by
  have h1 : orderOf g ∣ Nat.card (fusionOddCore H) :=
    Subgroup.orderOf_dvd_natCard (fusionOddCore H) hg
  have hodd : Odd (orderOf g) := Odd.of_dvd_nat (s3_odd_fusionOddCore H) h1
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 this

end OddCore

section Cent

variable {D : Type} [Group D] [Finite D] {t : D} {K : Subgroup D}

theorem DShape.orderOf_t (h : DShape D t K) : orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h.t_sq) h.t_ne

theorem DShape.K_comm (h : DShape D t K) {k : D} (hk : k ∈ K) : k * t = t * k := by
  have : k ∈ centralizer ({t} : Set D) := by
    rw [h.cent]
    exact mem_sup_right hk
  exact mem_centralizer_singleton_iff.1 this

theorem DShape.centEquiv (h : DShape D t K) :
    Nonempty (↥(centralizer ({t} : Set D)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) := by
  obtain ⟨eK⟩ := h.K_S5
  have hcomm : ∀ (a : ↥(zpowers t)) (k : ↥K), Commute ((zpowers t).subtype a) (K.subtype k) := by
    rintro ⟨a, n, rfl⟩ ⟨k, hk⟩
    exact ((Commute.symm (h.K_comm hk : k * t = t * k) : Commute t k).zpow_left n)
  let ψ : ↥(zpowers t) × ↥K →* D := (zpowers t).subtype.noncommCoprod K.subtype hcomm
  have hψ : ∀ p, ψ p = (p.1 : D) * (p.2 : D) := fun p => by
    simp [ψ, MonoidHom.noncommCoprod_apply]
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨⟨a, ha⟩, ⟨k, hk⟩⟩ hx
    rw [MonoidHom.mem_ker, hψ] at hx
    have hx' : a * k = 1 := hx
    have hak : a = k⁻¹ := eq_inv_of_mul_eq_one_left hx'
    have h1 : a ∈ K := by rw [hak]; exact K.inv_mem hk
    have : a = 1 := Subgroup.disjoint_def.1 h.disj ha h1
    have hk1 : k = 1 := by
      rw [this, one_mul] at hx'
      exact hx'
    simp only [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext this, Subtype.ext hk1⟩
  have hrange : ψ.range = centralizer ({t} : Set D) := by
    rw [h.cent]
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hψ]
      exact mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)
    · refine sup_le ?_ ?_
      · intro a ha
        exact ⟨(⟨a, ha⟩, 1), by rw [hψ]; simp⟩
      · intro k hk
        exact ⟨(1, ⟨k, hk⟩), by rw [hψ]; simp⟩
  have e1 : (↥(zpowers t) × ↥K) ≃* ↥ψ.range :=
    MulEquiv.ofBijective ψ.rangeRestrict ⟨by
      intro x y hxy
      exact hinj (congrArg Subtype.val hxy), ψ.rangeRestrict_surjective⟩
  have e2 : ↥ψ.range ≃* ↥(centralizer ({t} : Set D)) := MulEquiv.subgroupCongr hrange
  have hcard : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, h.orderOf_t]
  have : IsCyclic (zpowers t) := inferInstance
  let e3 : Multiplicative (ZMod 2) ≃* ↥(zpowers t) :=
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard.symm).toAddEquiv).trans
      (zmodCyclicMulEquiv inferInstance)
  exact ⟨((e1.trans e2).symm).trans (MulEquiv.prodCongr e3.symm eK)⟩

end Cent

section PA2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

@[expose] def PA2.tb (a : PA2 L t E z) : OQuot (Cen a.y) := oMk (Cen a.y) ⟨t, a.t_cy⟩

@[expose] def PA2.Kb (a : PA2 L t E z) : Subgroup (OQuot (Cen a.y)) :=
  (a.K₀.subgroupOf (Cen a.y)).map (oMk (Cen a.y))

omit [Finite G] in
theorem PA2.K₀_le_cen (a : PA2 L t E z) : a.K₀ ≤ Cen a.y := fun _ hx => (a.K₀_le hx).2

@[expose] def PA2.kmap (a : PA2 L t E z) : ↥a.K₀ →* OQuot (Cen a.y) :=
  (oMk (Cen a.y)).comp (Subgroup.inclusion a.K₀_le_cen)

omit [Finite G] in
theorem PA2.kmap_range (a : PA2 L t E z) : a.kmap.range = a.Kb := by
  unfold PA2.kmap PA2.Kb
  rw [MonoidHom.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact k.2
  · intro hx
    exact ⟨⟨x.1, hx⟩, rfl⟩

omit [Finite G] in
theorem PA2.card_K₀ (a : PA2 L t E z) : Nat.card ↥a.K₀ = 120 := by
  rw [Nat.card_congr a.eK₀.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

@[expose] noncomputable def PA2.kmapEquiv (a : PA2 L t E z) : ↥a.K₀ ≃* ↥a.Kb := by
  have hbij : Function.Bijective a.kmap.rangeRestrict := by
    refine ⟨?_, a.kmap.rangeRestrict_surjective⟩
    have hs := a.kmap.rangeRestrict_surjective.bijective_of_nat_card_le (by
      rw [a.card_K₀, Nat.card_congr (MulEquiv.subgroupCongr a.kmap_range).toEquiv]
      exact a.Kbar_card.symm.le)
    exact hs.1
  exact (MulEquiv.ofBijective a.kmap.rangeRestrict hbij).trans
    (MulEquiv.subgroupCongr a.kmap_range)

@[expose] noncomputable def PA2.eKb (a : PA2 L t E z) : ↥a.Kb ≃* Equiv.Perm (Fin 5) :=
  a.kmapEquiv.symm.trans a.eK₀

theorem PA2.eKb_kmapEquiv (a : PA2 L t E z) (x : ↥a.K₀) : a.eKb (a.kmapEquiv x) = a.eK₀ x := by
  simp [PA2.eKb]

omit [Finite G] in
theorem PA2.mem_Kb (a : PA2 L t E z) {x : G} (hx : x ∈ a.K₀) :
    oMk (Cen a.y) ⟨x, a.K₀_le_cen hx⟩ ∈ a.Kb :=
  ⟨⟨x, a.K₀_le_cen hx⟩, hx, rfl⟩

theorem PA2.dshape (hb : PAB G L t E W z) (a : PA2 L t E z) :
    DShape (OQuot (Cen a.y)) a.tb a.Kb where
  t_sq := by
    unfold PA2.tb
    rw [← map_mul]
    have : (⟨t, a.t_cy⟩ * ⟨t, a.t_cy⟩ : ↥(Cen a.y)) = 1 := Subtype.ext hb.t_mul_t
    rw [this, map_one]
  t_ne := by
    intro h1
    unfold PA2.tb at h1
    have h2 : (⟨t, a.t_cy⟩ : ↥(Cen a.y)) ∈ fusionOddCore ↥(Cen a.y) :=
      (QuotientGroup.eq_one_iff _).1 h1
    have h3 := s3_eq_one_of_sq_mem_oddCore h2 (Subtype.ext hb.t_mul_t)
    have h4 : t = 1 := congrArg Subtype.val h3
    have := hb.t_ord
    rw [h4, orderOf_one] at this
    exact absurd this (by decide)
  cent := a.Kbar_cent
  disj := a.Kbar_disj
  K_S5 := ⟨a.eKb⟩
  zstar := a.zstar_D

end PA2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
