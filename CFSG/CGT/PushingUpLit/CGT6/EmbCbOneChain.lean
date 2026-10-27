module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneZ
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneEnd
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneL

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem cbc_isKGroup_of_le {G K : Subgroup (MulAut V)} (hG : CFSG.IsKGroup ↥G) (hKG : K ≤ G) :
    CFSG.IsKGroup ↥K :=
  isKGroup_of_surjective (isKGroup_subgroup hG (K.subgroupOf G))
    (Subgroup.subgroupOfEquivOfLe hKG).toMonoidHom (Subgroup.subgroupOfEquivOfLe hKG).surjective

omit [Finite V] in
theorem cbc_commutator_eq_self_alt {b : ℕ} (hb : 2 ≤ b) {Z : Subgroup (MulAut V)}
    (θ : ↥Z ≃* alternatingGroup (Fin (2 * b + 1))) : ⁅Z, Z⁆ = Z :=
  Subgroup.isPerfect_iff.mp (CFSG.LocalCores.isQuasisimple_of_mulEquiv θ.symm
    (CFSG.CGT.PushingUpLit.Glue.isQuasisimple_alternating (k := 2 * b + 1) (by omega))).1

omit [Finite V] in
theorem cbc_centralizer_zpowers (z : MulAut V) :
    Subgroup.centralizer ((Subgroup.zpowers z : Subgroup (MulAut V)) : Set (MulAut V)) =
      Subgroup.centralizer ({z} : Set (MulAut V)) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

namespace OneCfg

variable {Y X G T : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ} (c : OneCfg G T Y t m X)

include c in
theorem eq_one_of_comm_L {z : MulAut V} (hzL : z ∈ conjClosure Y G)
    (h : ∀ l ∈ conjClosure Y G, z * l = l * z) : z = 1 := by
  have hz : (⟨z, hzL⟩ : ↥(conjClosure Y G)) ∈ Subgroup.center ↥(conjClosure Y G) :=
    Subgroup.mem_center_iff.mpr fun l => Subtype.ext (h l l.2).symm
  rw [c.L_center_eq_bot, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

include c in
theorem adm_Z {z : MulAut V} {Z : Subgroup (MulAut V)} {b : ℕ} (htz : t * z = z * t)
    (hZX : Z ≤ X) (hzZ : ∀ x ∈ Z, z * x = x * z) (htZ : ∀ x ∈ Z, t * x = x * t) (hb : 2 ≤ b)
    (θZ : ↥Z ≃* alternatingGroup (Fin (2 * b + 1)))
    (hnat : IsNatSectionWith (altAct (2 * b + 1)) θZ (commV Z) ⊥)
    (hnorm : ∀ g ∈ G, g * z = z * g → g * t = t * g → ∀ x ∈ Z, g * x * g⁻¹ ∈ Z) :
    Adm4 (G ⊓ Subgroup.centralizer ({z} : Set (MulAut V))) (Subgroup.zpowers t) Z := by
  have hTcent := cbc_centralizer_zpowers t
  have hZG : Z ≤ G := hZX.trans c.X_le_G
  have htH : t ∈ G ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) :=
    ⟨c.htG, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact htz.symm⟩
  have hYC : Z ≤ (G ⊓ Subgroup.centralizer ({z} : Set (MulAut V))) ⊓
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup (MulAut V)) : Set (MulAut V)) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hZG hx, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hzZ x hx
    · rw [hTcent, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact htZ x hx
  refine
    { hTG := Subgroup.zpowers_le.mpr htH
      hT1 := fun h0 => c.ht1 (Subgroup.zpowers_eq_bot.mp h0)
      hT2 := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime c.ht2 c.ht1, pow_one])
      hYC := hYC
      hsub := ?_
      hperf := cbc_commutator_eq_self_alt hb θZ
      hcls := classX4_of_natSection c.hV hb θZ hnat }
  refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
  have hg1 := g.2.1
  have hg2 : (g : MulAut V) ∈ Subgroup.centralizer ({t} : Set (MulAut V)) := by
    rw [← hTcent]
    exact g.2.2
  have hgz : (g : MulAut V) * z = z * g :=
    (Subgroup.mem_centralizer_iff.mp hg1.2 z (Set.mem_singleton z)).symm
  have hgt : (g : MulAut V) * t = t * g :=
    (Subgroup.mem_centralizer_iff.mp hg2 t (Set.mem_singleton t)).symm
  exact hnorm g hg1.1 hgz hgt n hn

include c in
theorem false_of_chain : False := by
  classical
  obtain ⟨z, Z, b, hzX, hz1, hz2, htz, hZX, hzZ, htZ, hb, ⟨θZ, hnat⟩, hnorm⟩ := c.exists_zZ
  have hLG : conjClosure Y G ≤ G := c.L_le_G
  have hYL : Y ≤ conjClosure Y G := le_conjClosure
  have hzL : z ∈ conjClosure Y G := c.hX.le_conjClosure c.hm c.hY hzX
  have hZ1 : ⁅Z, Z⁆ = Z := cbc_commutator_eq_self_alt hb θZ
  have hZcls : ClassX4 Z := classX4_of_natSection c.hV hb θZ hnat
  have hZL : Z ≠ conjClosure Y G := by
    intro hZL
    exact hz1 (c.eq_one_of_comm_L hzL fun l hl => hzZ l (hZL ▸ hl))
  set H : Subgroup (MulAut V) := G ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) with hH
  have hHG : H ≤ G := inf_le_left
  have hHne : H ≠ G := by
    intro heq
    refine hz1 (c.eq_one_of_comm_L hzL fun l hl => ?_)
    have hlH : l ∈ H := by
      rw [heq]
      exact hLG hl
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hlH).2 z (Set.mem_singleton z)
  have hsmaller : Smaller H G := Or.inl (Subgroup.card_lt_of_lt (lt_of_le_of_ne hHG hHne))
  have hadm := c.adm_Z htz hZX hzZ htZ hb θZ hnat hnorm
  obtain ⟨Z', hlift⟩ := c.cfg.ih V c.hV H hsmaller (cbc_isKGroup_of_le c.cfg.kgroup hHG)
    (Subgroup.zpowers t) Z hadm
  have hZ'perf : ⁅Z', Z'⁆ = Z' := Lift4.commutator_eq_self c.hV hZ1 hZcls hlift
  have hZ'H : Z' ≤ H := hlift.2.1
  have hZ'L : Z' ≤ conjClosure Y G := c.perfect_le_L (hZ'H.trans hHG) hZ'perf
  have hZZ' : Z ≤ Z' := hlift.1
  have hlift' : Lift4 (conjClosure Y G ⊓ H) Z Z' :=
    ⟨hZZ', le_inf hZ'L hZ'H,
      CFSG.GroupTheory.isSubnormal_subgroupOf_of_le inf_le_right hlift.2.2.1, hlift.2.2.2⟩
  have hsmallerL : Smaller (conjClosure Y G) G := Or.inl (Subgroup.card_lt_of_lt c.L_lt_G)
  have hZcent := cbc_centralizer_zpowers z
  have hadm2 : Adm4 (conjClosure Y G) (Subgroup.zpowers z) Z' :=
    { hTG := Subgroup.zpowers_le.mpr hzL
      hT1 := fun h0 => hz1 (Subgroup.zpowers_eq_bot.mp h0)
      hT2 := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one])
      hYC := by
        intro x hx
        refine Subgroup.mem_inf.mpr ⟨hZ'L hx, ?_⟩
        rw [hZcent]
        exact (Subgroup.mem_inf.mp (hZ'H hx)).2
      hsub := by
        refine CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (K := H) ?_ hlift.2.2.1
        intro x hx
        have hx' := Subgroup.mem_inf.mp hx
        refine Subgroup.mem_inf.mpr ⟨hLG hx'.1, ?_⟩
        rw [← hZcent]
        exact hx'.2
      hperf := hZ'perf
      hcls := hlift.classX4 }
  obtain ⟨Xh, hlift2⟩ := c.cfg.ih V c.hV (conjClosure Y G) hsmallerL
    (cbc_isKGroup_of_le c.cfg.kgroup hLG) (Subgroup.zpowers z) Z' hadm2
  have hXhL : Xh ≤ conjClosure Y G := hlift2.2.1
  have hZ'Xh : Z' ≤ Xh := hlift2.1
  have hXh : Xh = conjClosure Y G := by
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup c.L_simple hlift2.2.2.1 with
      hbot | htop
    · exfalso
      have : Nontrivial (alternatingGroup (Fin (2 * b + 1))) :=
        alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
      have : Nontrivial ↥Z := θZ.toEquiv.nontrivial
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥Z)
      have hxXh : (x : MulAut V) ∈ Xh := hZ'Xh (hZZ' x.2)
      have h1 : (⟨(x : MulAut V), hXhL hxXh⟩ : ↥(conjClosure Y G)) ∈
          Xh.subgroupOf (conjClosure Y G) := hxXh
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : (x : MulAut V) = 1 := congrArg Subtype.val h1
      exact hx (Subtype.ext h2)
    · refine le_antisymm hXhL fun l hl => ?_
      have h1 : (⟨l, hl⟩ : ↥(conjClosure Y G)) ∈ Xh.subgroupOf (conjClosure Y G) := by
        rw [htop]
        trivial
      exact h1
  have hlift2' : Lift4 (conjClosure Y G) Z' (conjClosure Y G) := by
    have h := hlift2
    rwa [hXh] at h
  have hlift3 : Lift4 (conjClosure Y G) Z (conjClosure Y G) :=
    Lift4.trans c.hV hZ1 hZcls hlift' inf_le_left hlift2'
  exact EndCfg4.false_of_natural_lift c.hNL c.cfg c.hV c.hm c.hodd c.hY hYL hLG
    (cbo_conjClosure_normal G Y) c.L_perfect c.L_center_eq_bot hb θZ hnat hZL hlift3

end OneCfg

end CFSG.CGT.PushingUpLit.CGT6
