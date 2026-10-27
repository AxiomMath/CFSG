module

public import CFSG.GH74.QTGen4.U42.CentralExt

public section

namespace CFSG.GH74.QTGen4.U42

section Pullback

variable {H H' : Type*} [Group H] [Group H']

def pb (z : H) (z' : H') [(Subgroup.zpowers z).Normal] [(Subgroup.zpowers z').Normal]
    (θbar : H ⧸ Subgroup.zpowers z ≃* H' ⧸ Subgroup.zpowers z') : Subgroup (H × H') where
  carrier := {p | (QuotientGroup.mk p.2 : H' ⧸ Subgroup.zpowers z') = θbar (QuotientGroup.mk p.1)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, QuotientGroup.mk_mul] at ha hb ⊢
    rw [ha, hb, map_mul]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv, QuotientGroup.mk_inv] at ha ⊢
    rw [ha, map_inv]

theorem mem_pb (z : H) (z' : H') [(Subgroup.zpowers z).Normal] [(Subgroup.zpowers z').Normal]
    (θbar : H ⧸ Subgroup.zpowers z ≃* H' ⧸ Subgroup.zpowers z') (p : H × H') :
    p ∈ pb z z' θbar ↔
      (QuotientGroup.mk p.2 : H' ⧸ Subgroup.zpowers z') = θbar (QuotientGroup.mk p.1) :=
  Iff.rfl

theorem zz_mem (z : H) (z' : H') [(Subgroup.zpowers z).Normal] [(Subgroup.zpowers z').Normal]
    (θbar : H ⧸ Subgroup.zpowers z ≃* H' ⧸ Subgroup.zpowers z') :
    (z, z') ∈ pb z z' θbar := by
  rw [mem_pb]
  have h1 : (QuotientGroup.mk z : H ⧸ Subgroup.zpowers z) = 1 :=
    (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
  have h2 : (QuotientGroup.mk z' : H' ⧸ Subgroup.zpowers z') = 1 :=
    (QuotientGroup.eq_one_iff z').mpr (Subgroup.mem_zpowers z')
  show (QuotientGroup.mk z' : H' ⧸ Subgroup.zpowers z') = θbar (QuotientGroup.mk z)
  rw [h1, h2, map_one]

def Zp (z : H) (z' : H') : Subgroup (H × H') := (Subgroup.zpowers z).prod (Subgroup.zpowers z')

theorem Zp_normal (z : H) (z' : H') [(Subgroup.zpowers z).Normal] [(Subgroup.zpowers z').Normal] :
    (Zp z z').Normal where
  conj_mem n hn g := by
    rcases Subgroup.mem_prod.mp hn with ⟨h1, h2⟩
    exact Subgroup.mem_prod.mpr
      ⟨(inferInstance : (Subgroup.zpowers z).Normal).conj_mem _ h1 _,
        (inferInstance : (Subgroup.zpowers z').Normal).conj_mem _ h2 _⟩

theorem commute_of_mem_zpowers {G : Type*} [Group G] {g x y : G}
    (hx : x ∈ Subgroup.zpowers g) (hy : y ∈ Subgroup.zpowers g) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_zpow_self g a b).eq

def dW (z : H) (z' : H') [(Subgroup.zpowers z).Normal] [(Subgroup.zpowers z').Normal]
    (θbar : H ⧸ Subgroup.zpowers z ≃* H' ⧸ Subgroup.zpowers z') : pb z z' θbar :=
  ⟨(z, z'), zz_mem z z' θbar⟩

theorem iso_of_complement (z : H) (z' : H') [(Subgroup.zpowers z).Normal]
    [(Subgroup.zpowers z').Normal] (ho : orderOf z = 2) (ho' : orderOf z' = 2)
    (θbar : H ⧸ Subgroup.zpowers z ≃* H' ⧸ Subgroup.zpowers z')
    (C : Subgroup (pb z z' θbar))
    (hC1 : Subgroup.zpowers (dW z z' θbar) ≤ C)
    (hC2 : C ⊓ Subgroup.comap (pb z z' θbar).subtype (Zp z z') =
      Subgroup.zpowers (dW z z' θbar))
    (hC3 : C ⊔ Subgroup.comap (pb z z' θbar).subtype (Zp z z') = ⊤) :
    ∃ θ : H ≃* H', ∀ h : H, QuotientGroup.mk (θ h) = θbar (QuotientGroup.mk h) := by
  haveI := Zp_normal z z'
  haveI : (Subgroup.comap (pb z z' θbar).subtype (Zp z z')).Normal :=
    Subgroup.Normal.comap (Zp_normal z z') _
  have hfst_zpow : ∀ (x : H × H') (k : ℤ), (x ^ k).1 = x.1 ^ k :=
    fun x k => map_zpow (MonoidHom.fst H H') x k
  have hsnd_zpow : ∀ (x : H × H') (k : ℤ), (x ^ k).2 = x.2 ^ k :=
    fun x k => map_zpow (MonoidHom.snd H H') x k
  have hdk : ∀ k : ℤ, ((dW z z' θbar ^ k : pb z z' θbar) : H × H') = (z ^ k, z' ^ k) :=
    fun k => Prod.ext (hfst_zpow _ k) (hsnd_zpow _ k)
  have hzk : ∀ k : ℤ, z ^ k = 1 ↔ (2 : ℤ) ∣ k := fun k => by
    rw [← orderOf_dvd_iff_zpow_eq_one, ho]; norm_num
  have hzk' : ∀ k : ℤ, z' ^ k = 1 ↔ (2 : ℤ) ∣ k := fun k => by
    rw [← orderOf_dvd_iff_zpow_eq_one, ho']; norm_num
  have hZC : ∀ c : C, ((c : pb z z' θbar) : H × H') ∈ Zp z z' →
      ∃ k : ℤ, ((c : pb z z' θbar) : H × H') = (z ^ k, z' ^ k) := by
    intro c hc
    have hmem : (c : pb z z' θbar) ∈ C ⊓ Subgroup.comap (pb z z' θbar).subtype (Zp z z') :=
      ⟨c.2, hc⟩
    rw [hC2] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact ⟨k, by rw [← hk, hdk]⟩
  let p1 : C →* H := (MonoidHom.fst H H').comp ((pb z z' θbar).subtype.comp C.subtype)
  let p2 : C →* H' := (MonoidHom.snd H H').comp ((pb z z' θbar).subtype.comp C.subtype)
  have hp1 : Function.Bijective p1 := by
    constructor
    · rw [injective_iff_map_eq_one p1]
      intro c hc
      have hc1 : ((c : pb z z' θbar) : H × H').1 = 1 := hc
      have hθ : θbar (QuotientGroup.mk ((c : pb z z' θbar) : H × H').1) = 1 := by
        rw [hc1, (QuotientGroup.eq_one_iff (1 : H)).mpr (Subgroup.one_mem _), map_one]
      have hW' := (mem_pb z z' θbar _).mp (c : pb z z' θbar).2
      rw [hθ] at hW'
      have hZp : ((c : pb z z' θbar) : H × H') ∈ Zp z z' :=
        Subgroup.mem_prod.mpr ⟨by rw [hc1]; exact Subgroup.one_mem _,
          (QuotientGroup.eq_one_iff _).mp hW'⟩
      obtain ⟨k, hk⟩ := hZC c hZp
      have hk1 : z ^ k = 1 := by
        have := congrArg Prod.fst hk
        rw [hc1] at this
        exact this.symm
      have hk2 : z' ^ k = 1 := (hzk' k).mpr ((hzk k).mp hk1)
      refine Subtype.ext (Subtype.ext ?_)
      show ((c : pb z z' θbar) : H × H') = 1
      rw [hk]
      exact Prod.ext (by simpa using hk1) (by simpa using hk2)
    · intro h
      obtain ⟨h', hh'⟩ := QuotientGroup.mk_surjective (θbar (QuotientGroup.mk h))
      have hw : (⟨(h, h'), (mem_pb z z' θbar _).mpr hh'⟩ : pb z z' θbar) ∈
          C ⊔ Subgroup.comap (pb z z' θbar).subtype (Zp z z') := by
        rw [hC3]; exact Subgroup.mem_top _
      obtain ⟨c, hc, e, he, hce⟩ := Subgroup.mem_sup_of_normal_right.mp hw
      have he' : ((e : pb z z' θbar) : H × H') ∈ Zp z z' := he
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_prod.mp he').1
      have hcC : c * dW z z' θbar ^ a ∈ C :=
        C.mul_mem hc (hC1 ((Subgroup.zpowers (dW z z' θbar)).zpow_mem (Subgroup.mem_zpowers _) a))
      refine ⟨⟨c * dW z z' θbar ^ a, hcC⟩, ?_⟩
      have hfin : ((c : pb z z' θbar) : H × H').1 * ((e : pb z z' θbar) : H × H').1 = h := by
        have := congrArg (fun x : pb z z' θbar => ((x : pb z z' θbar) : H × H').1) hce
        simp only [Subgroup.coe_mul, Prod.fst_mul] at this
        exact this
      show ((c * dW z z' θbar ^ a : pb z z' θbar) : H × H').1 = h
      rw [Subgroup.coe_mul, Prod.fst_mul, hdk a]
      dsimp only
      rw [← ha] at hfin
      exact hfin
  have hp2 : Function.Bijective p2 := by
    constructor
    · rw [injective_iff_map_eq_one p2]
      intro c hc
      have hc2 : ((c : pb z z' θbar) : H × H').2 = 1 := hc
      have hW' := (mem_pb z z' θbar _).mp (c : pb z z' θbar).2
      rw [hc2, (QuotientGroup.eq_one_iff (1 : H')).mpr (Subgroup.one_mem _)] at hW'
      have hθ : QuotientGroup.mk ((c : pb z z' θbar) : H × H').1 = (1 : H ⧸ Subgroup.zpowers z) :=
        θbar.injective (by rw [map_one]; exact hW'.symm)
      have hZp : ((c : pb z z' θbar) : H × H') ∈ Zp z z' :=
        Subgroup.mem_prod.mpr ⟨(QuotientGroup.eq_one_iff _).mp hθ,
          by rw [hc2]; exact Subgroup.one_mem _⟩
      obtain ⟨k, hk⟩ := hZC c hZp
      have hk2 : z' ^ k = 1 := by
        have := congrArg Prod.snd hk
        rw [hc2] at this
        exact this.symm
      have hk1 : z ^ k = 1 := (hzk k).mpr ((hzk' k).mp hk2)
      refine Subtype.ext (Subtype.ext ?_)
      show ((c : pb z z' θbar) : H × H') = 1
      rw [hk]
      exact Prod.ext (by simpa using hk1) (by simpa using hk2)
    · intro h'
      obtain ⟨hq, hh⟩ := θbar.surjective (QuotientGroup.mk h')
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective hq
      have hw : (⟨(h, h'), (mem_pb z z' θbar _).mpr hh.symm⟩ : pb z z' θbar) ∈
          C ⊔ Subgroup.comap (pb z z' θbar).subtype (Zp z z') := by
        rw [hC3]; exact Subgroup.mem_top _
      obtain ⟨c, hc, e, he, hce⟩ := Subgroup.mem_sup_of_normal_right.mp hw
      have he' : ((e : pb z z' θbar) : H × H') ∈ Zp z z' := he
      obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_prod.mp he').2
      have hcC : c * dW z z' θbar ^ b ∈ C :=
        C.mul_mem hc (hC1 ((Subgroup.zpowers (dW z z' θbar)).zpow_mem (Subgroup.mem_zpowers _) b))
      refine ⟨⟨c * dW z z' θbar ^ b, hcC⟩, ?_⟩
      have hfin : ((c : pb z z' θbar) : H × H').2 * ((e : pb z z' θbar) : H × H').2 = h' := by
        have := congrArg (fun x : pb z z' θbar => ((x : pb z z' θbar) : H × H').2) hce
        simp only [Subgroup.coe_mul, Prod.snd_mul] at this
        exact this
      show ((c * dW z z' θbar ^ b : pb z z' θbar) : H × H').2 = h'
      rw [Subgroup.coe_mul, Prod.snd_mul, hdk b]
      dsimp only
      rw [← hb] at hfin
      exact hfin
  refine ⟨(MulEquiv.ofBijective p1 hp1).symm.trans (MulEquiv.ofBijective p2 hp2), fun h => ?_⟩
  obtain ⟨c, hc⟩ := (MulEquiv.ofBijective p1 hp1).surjective h
  have hθ : ((MulEquiv.ofBijective p1 hp1).symm.trans (MulEquiv.ofBijective p2 hp2)) h = p2 c := by
    rw [← hc, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  rw [hθ, ← hc]
  exact (mem_pb z z' θbar _).mp (c : pb z z' θbar).2

section Main

theorem orderOf_two_parity {G : Type*} [Group G] (g : G) (hg : orderOf g = 2) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g := by
  have h := zpow_mod_orderOf g k
  rw [hg] at h
  push_cast at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [← h, h0, zpow_zero]
  · right; rw [← h, h1, zpow_one]

theorem normal_zpowers_of_mem_center {G : Type*} [Group G] (g : G)
    (hg : g ∈ Subgroup.center G) : (Subgroup.zpowers g).Normal where
  conj_mem n hn x := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute x g := Subgroup.mem_center_iff.mp hg x
    have hc' : x * g ^ k = g ^ k * x := (hc.zpow_right k).eq
    rw [hc', mul_assoc, mul_inv_cancel, mul_one]
    exact (Subgroup.zpowers g).zpow_mem (Subgroup.mem_zpowers g) k

theorem z_mem_T {H : Type*} [Group H] (z : H) (hz : z ∈ Subgroup.center H) (ho : orderOf z = 2)
    (T : Subgroup H) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) : z ∈ T := by
  haveI := normal_zpowers_of_mem_center z hz
  have hzP : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho]; norm_num)
  have hzS : Subgroup.zpowers z ≤ (hT.toSylow hTi : Subgroup H) :=
    IsPGroup.le_sylow_of_normal hzP (hT.toSylow hTi)
  rw [IsPGroup.toSylow_coe hT hTi] at hzS
  exact hzS (Subgroup.mem_zpowers z)

theorem theta_z_eq {H H' : Type*} [Group H] [Group H'] (z : H) (z' : H')
    [(Subgroup.zpowers z).Normal] [(Subgroup.zpowers z').Normal]
    (ho : orderOf z = 2) (ho' : orderOf z' = 2)
    (T : Subgroup H) (hTz : z ∈ T) (T' : Subgroup H') (θT : T ≃* T')
    (θbar : H ⧸ Subgroup.zpowers z ≃* H' ⧸ Subgroup.zpowers z')
    (hcomp : ∀ t : T, θbar (QuotientGroup.mk (t : H)) = QuotientGroup.mk (θT t : H')) :
    ((θT ⟨z, hTz⟩ : T') : H') = z' := by
  set a : T := ⟨z, hTz⟩ with ha
  have hza : (a : H) = z := rfl
  have hmem : ((θT a : T') : H') ∈ Subgroup.zpowers z' := by
    rw [← QuotientGroup.eq_one_iff, ← hcomp a, hza,
      (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z), map_one]
  have hne : ((θT a : T') : H') ≠ 1 := by
    intro h1
    have h2 : θT a = 1 := Subtype.ext (by simpa using h1)
    have h3 : a = 1 := θT.injective (h2.trans (map_one θT).symm)
    have h4 : z = 1 := by simpa [hza] using congrArg Subtype.val h3
    rw [h4, orderOf_one] at ho
    norm_num at ho
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rcases orderOf_two_parity z' ho' k with h | h
  · exact absurd (hk.symm.trans h) hne
  · exact hk.symm.trans h

theorem theta_zpow_eq {H H' : Type*} [Group H] [Group H'] (z : H) (z' : H')
    [(Subgroup.zpowers z).Normal] [(Subgroup.zpowers z').Normal]
    (ho : orderOf z = 2) (ho' : orderOf z' = 2)
    (T : Subgroup H) (hTz : z ∈ T) (T' : Subgroup H') (θT : T ≃* T')
    (θbar : H ⧸ Subgroup.zpowers z ≃* H' ⧸ Subgroup.zpowers z')
    (hcomp : ∀ t : T, θbar (QuotientGroup.mk (t : H)) = QuotientGroup.mk (θT t : H'))
    (a : ℤ) (ha : z ^ a ∈ T) :
    ((θT ⟨z ^ a, ha⟩ : T') : H') = z' ^ a := by
  have e : (⟨z ^ a, ha⟩ : T) = (⟨z, hTz⟩ : T) ^ a := Subtype.ext (by simp)
  rw [e, map_zpow, Subgroup.coe_zpow, theta_z_eq z z' ho ho' T hTz T' θT θbar hcomp]

theorem dW_mem_center {H H' : Type*} [Group H] [Group H'] (z : H) (z' : H')
    [(Subgroup.zpowers z).Normal] [(Subgroup.zpowers z').Normal]
    (hz : z ∈ Subgroup.center H) (hz' : z' ∈ Subgroup.center H')
    (θbar : H ⧸ Subgroup.zpowers z ≃* H' ⧸ Subgroup.zpowers z') :
    dW z z' θbar ∈ Subgroup.center (pb z z' θbar) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Prod.ext
  · show g.1.1 * z = z * g.1.1
    exact Subgroup.mem_center_iff.mp hz _
  · show g.1.2 * z' = z' * g.1.2
    exact Subgroup.mem_center_iff.mp hz' _

theorem sq_eq_one_of_mem_zpowers {G : Type*} [Group G] (z : G) (ho : orderOf z = 2) (x : G)
    (hx : x ∈ Subgroup.zpowers z) : x ^ 2 = 1 := by
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ 2 = 1 := by rw [← ho]; exact pow_orderOf_eq_one z
  rcases orderOf_two_parity z ho a with h | h
  · rw [h, one_pow]
  · rw [h, h2]

theorem isPGroup_two_of_sq {G : Type*} [Group G] (S : Subgroup G) (h : ∀ x ∈ S, x ^ 2 = 1) :
    IsPGroup 2 S := by
  refine (IsPGroup.iff_orderOf).mpr fun g => ?_
  have hg2 : (g : S) ^ 2 = 1 := Subtype.ext (by simpa using h (g : G) g.2)
  have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · exact ⟨0, by rw [h1]; norm_num⟩
  · exact ⟨1, by rw [h1]; norm_num⟩

theorem dW_zpow_val {H H' : Type*} [Group H] [Group H'] (z : H) (z' : H')
    [(Subgroup.zpowers z).Normal] [(Subgroup.zpowers z').Normal]
    (θbar : H ⧸ Subgroup.zpowers z ≃* H' ⧸ Subgroup.zpowers z') (a : ℤ) :
    ((dW z z' θbar ^ a : pb z z' θbar) : H × H') = (z ^ a, z' ^ a) := by
  rw [Subgroup.coe_zpow]
  exact Prod.ext (map_zpow (MonoidHom.fst H H') (z, z') a)
    (map_zpow (MonoidHom.snd H H') (z, z') a)

theorem central_extension_rigidity {H H' : Type*} [Group H] [Group H'] [Finite H] [Finite H']
    (z : H) (z' : H') [(Subgroup.zpowers z).Normal] [(Subgroup.zpowers z').Normal]
    (hz : z ∈ Subgroup.center H) (hz' : z' ∈ Subgroup.center H')
    (ho : orderOf z = 2) (ho' : orderOf z' = 2)
    (T : Subgroup H) (T' : Subgroup H') (hT : IsPGroup 2 T) (hT' : IsPGroup 2 T')
    (hTi : ¬ 2 ∣ T.index) (hTi' : ¬ 2 ∣ T'.index)
    (θbar : H ⧸ Subgroup.zpowers z ≃* H' ⧸ Subgroup.zpowers z') (θT : ↥T ≃* ↥T')
    (hcomp : ∀ t : ↥T, θbar (QuotientGroup.mk (t : H)) = QuotientGroup.mk (θT t : H')) :
    ∃ θ : H ≃* H', ∀ h : H, QuotientGroup.mk (θ h) = θbar (QuotientGroup.mk h) := by
  have hzT : z ∈ T := z_mem_T z hz ho T hT hTi
  haveI hΔn : (Subgroup.zpowers (dW z z' θbar)).Normal :=
    normal_zpowers_of_mem_center _ (dW_mem_center z z' hz hz' θbar)
  haveI hV0n : (Subgroup.comap (pb z z' θbar).subtype (Zp z z')).Normal :=
    Subgroup.Normal.comap (Zp_normal z z') _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥T →* ↥(pb z z' θbar), ∀ t : ↥T,
      ((ψ t : ↥(pb z z' θbar)) : H × H') = ((t : H), (θT t : H')) := by
    refine ⟨MonoidHom.mk' (fun t : ↥T => (⟨((t : H), (θT t : H')),
      (mem_pb z z' θbar _).mpr (hcomp t).symm⟩ : ↥(pb z z' θbar))) ?_, fun t => rfl⟩
    intro a b
    apply Subtype.ext
    exact Prod.ext (by simp [map_mul]) (by simp [map_mul])
  obtain ⟨K0, hK0⟩ : ∃ K : Subgroup ↥(pb z z' θbar), K = (⊤ : Subgroup ↥T).map ψ := ⟨_, rfl⟩
  obtain ⟨Q0, hQ0⟩ : ∃ Q : Subgroup ↥(pb z z' θbar),
      Q = Subgroup.comap ((MonoidHom.fst H H').comp (pb z z' θbar).subtype) T := ⟨_, rfl⟩
  have hψK : ∀ t : ↥T, ψ t ∈ K0 := fun t => by
    rw [hK0]; exact Subgroup.mem_map.mpr ⟨t, Subgroup.mem_top t, rfl⟩
  have hZ : ((z, z') : H × H') ∈ Zp z z' :=
    Subgroup.mem_prod.mpr ⟨Subgroup.mem_zpowers z, Subgroup.mem_zpowers z'⟩
  have hdV : dW z z' θbar ∈ Subgroup.comap (pb z z' θbar).subtype (Zp z z') := hZ
  have hΔV : Subgroup.zpowers (dW z z' θbar) ≤ Subgroup.comap (pb z z' θbar).subtype (Zp z z') :=
    Subgroup.zpowers_le.mpr hdV
  have hVcomm : ∀ a ∈ Subgroup.comap (pb z z' θbar).subtype (Zp z z'),
      ∀ b ∈ Subgroup.comap (pb z z' θbar).subtype (Zp z z'), a * b = b * a := by
    intro a ha b hb
    have ha' : ((a : ↥(pb z z' θbar)) : H × H') ∈ Zp z z' := ha
    have hb' : ((b : ↥(pb z z' θbar)) : H × H') ∈ Zp z z' := hb
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_prod.mp ha'
    obtain ⟨hb1, hb2⟩ := Subgroup.mem_prod.mp hb'
    apply Subtype.ext
    apply Prod.ext
    · exact commute_of_mem_zpowers ha1 hb1
    · exact commute_of_mem_zpowers ha2 hb2
  have hV2 : IsPGroup 2 (Subgroup.comap (pb z z' θbar).subtype (Zp z z')) := by
    apply isPGroup_two_of_sq
    intro x hx
    have hx' : ((x : ↥(pb z z' θbar)) : H × H') ∈ Zp z z' := hx
    obtain ⟨h1', h2'⟩ := Subgroup.mem_prod.mp hx'
    apply Subtype.ext
    apply Prod.ext
    · simpa using sq_eq_one_of_mem_zpowers z ho _ h1'
    · simpa using sq_eq_one_of_mem_zpowers z' ho' _ h2'
  have htop : IsPGroup 2 (⊤ : Subgroup ↥T) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_congr (Subgroup.topEquiv.toEquiv)]; exact hn)
  have hK02 : IsPGroup 2 K0 := by rw [hK0]; exact IsPGroup.map htop ψ
  have hπsurj : Function.Surjective ((MonoidHom.fst H H').comp (pb z z' θbar).subtype) := by
    intro h
    obtain ⟨h', hh'⟩ := QuotientGroup.mk_surjective (θbar (QuotientGroup.mk h))
    exact ⟨⟨(h, h'), (mem_pb z z' θbar _).mpr hh'⟩, rfl⟩
  have hQi : ¬ 2 ∣ Q0.index := by
    rw [hQ0, Subgroup.index_comap_of_surjective T hπsurj]; exact hTi
  have hQeq : Q0 = Subgroup.comap (pb z z' θbar).subtype (Zp z z') ⊔ K0 := by
    apply le_antisymm
    · intro x hx
      rw [hQ0] at hx
      have hxT : ((x : ↥(pb z z' θbar)) : H × H').1 ∈ T := hx
      obtain ⟨t, ht⟩ : ∃ t : ↥T, (t : H) = ((x : ↥(pb z z' θbar)) : H × H').1 :=
        ⟨⟨_, hxT⟩, rfl⟩
      have hxW := (mem_pb z z' θbar _).mp (x : ↥(pb z z' θbar)).2
      have hmk : (QuotientGroup.mk (θT t : H') : H' ⧸ Subgroup.zpowers z') =
          QuotientGroup.mk ((x : ↥(pb z z' θbar)) : H × H').2 := by
        rw [← hcomp t, ht, hxW]
      have h1c : ((x * (ψ t)⁻¹ : ↥(pb z z' θbar)) : H × H').1 =
          ((x : ↥(pb z z' θbar)) : H × H').1 * (t : H)⁻¹ := by
        rw [Subgroup.coe_mul, Prod.fst_mul, Subgroup.coe_inv, Prod.fst_inv, hψ t]
      have h2c : ((x * (ψ t)⁻¹ : ↥(pb z z' θbar)) : H × H').2 =
          ((x : ↥(pb z z' θbar)) : H × H').2 * (θT t : H')⁻¹ := by
        rw [Subgroup.coe_mul, Prod.snd_mul, Subgroup.coe_inv, Prod.snd_inv, hψ t]
      have hz2 : (QuotientGroup.mk (((x : ↥(pb z z' θbar)) : H × H').2 * (θT t : H')⁻¹) :
          H' ⧸ Subgroup.zpowers z') = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hmk, mul_inv_cancel]
      have hv : x * (ψ t)⁻¹ ∈ Subgroup.comap (pb z z' θbar).subtype (Zp z z') := by
        show ((x * (ψ t)⁻¹ : ↥(pb z z' θbar)) : H × H') ∈ Zp z z'
        refine Subgroup.mem_prod.mpr ⟨?_, ?_⟩
        · rw [h1c, ← ht, mul_inv_cancel]; exact Subgroup.one_mem _
        · rw [h2c]; exact (QuotientGroup.eq_one_iff _).mp hz2
      have := Subgroup.mul_mem_sup hv (hψK t)
      rwa [inv_mul_cancel_right] at this
    · apply sup_le
      · intro x hx
        have hx' : ((x : ↥(pb z z' θbar)) : H × H') ∈ Zp z z' := hx
        obtain ⟨h1', _⟩ := Subgroup.mem_prod.mp hx'
        rw [hQ0]
        exact (Subgroup.zpowers_le.mpr hzT) h1'
      · intro k hk
        rw [hK0] at hk
        obtain ⟨t, _, rfl⟩ := Subgroup.mem_map.mp hk
        rw [hQ0]
        show ((ψ t : ↥(pb z z' θbar)) : H × H').1 ∈ T
        rw [hψ t]
        exact t.2
  have h1 : ∀ x ∈ Subgroup.comap (pb z z' θbar).subtype (Zp z z'), x ∈ K0 →
      x ∈ Subgroup.zpowers (dW z z' θbar) := by
    intro x hxV hxK
    rw [hK0] at hxK
    obtain ⟨t, _, hteq⟩ := Subgroup.mem_map.mp hxK
    have hxZ : ((x : ↥(pb z z' θbar)) : H × H') ∈ Zp z z' := hxV
    have hx1 : ((x : ↥(pb z z' θbar)) : H × H').1 = (t : H) := by
      rw [← hteq, hψ t]
    have hx2 : ((x : ↥(pb z z' θbar)) : H × H').2 = (θT t : H') := by
      rw [← hteq, hψ t]
    have ht1 : (t : H) ∈ Subgroup.zpowers z := by
      rw [← hx1]; exact (Subgroup.mem_prod.mp hxZ).1
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp ht1
    have hta : z ^ a ∈ T := by rw [ha]; exact t.2
    have htE : t = ⟨z ^ a, hta⟩ := Subtype.ext ha.symm
    have hθa : ((θT t : T') : H') = z' ^ a := by
      rw [htE]; exact theta_zpow_eq z z' ho ho' T hzT T' θT θbar hcomp a hta
    have hxeq : ((x : ↥(pb z z' θbar)) : H × H') = (z ^ a, z' ^ a) :=
      Prod.ext (hx1.trans ha.symm) (hx2.trans hθa)
    refine Subgroup.mem_zpowers_iff.mpr ⟨a, Subtype.ext ?_⟩
    rw [dW_zpow_val, hxeq]
  obtain ⟨C, hΔC, hC2, hC3⟩ := exists_complement_mod_central
    (Subgroup.zpowers (dW z z' θbar)) (Subgroup.comap (pb z z' θbar).subtype (Zp z z'))
    K0 Q0 hΔV hVcomm hV2 hK02 hQeq hQi h1
  exact iso_of_complement z z' ho ho' θbar C hΔC hC2 hC3

end Main

end Pullback

end CFSG.GH74.QTGen4.U42

end
