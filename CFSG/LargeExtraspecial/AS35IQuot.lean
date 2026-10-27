module

public import CFSG.LargeExtraspecial.AS35IAbs

public section

namespace CFSG.LargeExtraspecial.Asc22

open Subgroup Asc77

variable {G : Type} [Group G]

abbrev kerK (N : Subgroup G) (z : G) : Subgroup N := (conjAct z N).ker

abbrev Gbar (N : Subgroup G) (z : G) : Type := ↥N ⧸ kerK N z

abbrev piK (N : Subgroup G) (z : G) : ↥N →* Gbar N z := QuotientGroup.mk' (kerK N z)

abbrev barOf (N : Subgroup G) (z : G) (X : Subgroup G) : Subgroup (Gbar N z) :=
  (X.subgroupOf N).map (piK N z)

variable {N : Subgroup G} {z : G}

theorem mem_kerK {n : N} : n ∈ kerK N z ↔ (n : G) ∈ kerV N z := by
  rw [Hyp.mem_kerV_iff n.2, MonoidHom.mem_ker]
  constructor
  · intro h1 t ht
    have h2 := congrArg (fun σ : Equiv.Perm (conjIn z N) => ((σ ⟨t, ht⟩ : conjIn z N) : G)) h1
    simp only [conjAct_apply, Equiv.Perm.coe_one, id_eq] at h2
    calc t * (n : G) = (n : G) * t * (n : G)⁻¹ * n := by rw [h2]
      _ = (n : G) * t := by group
  · intro h1
    ext ⟨t, ht⟩
    simp only [conjAct_apply, Equiv.Perm.coe_one, id_eq]
    rw [← h1 t ht]
    group

theorem piK_surjective : Function.Surjective (piK N z) := QuotientGroup.mk'_surjective _

theorem piK_eq_one {n : N} : piK N z n = 1 ↔ (n : G) ∈ kerV N z := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_kerK]

theorem piK_eq_iff {n m : N} : piK N z n = piK N z m ↔ (n : G)⁻¹ * m ∈ kerV N z := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_kerK]
  simp

theorem piK_mem_barOf {X : Subgroup G} {n : N} (hn : (n : G) ∈ X) :
    piK N z n ∈ barOf N z X :=
  ⟨n, mem_subgroupOf.2 hn, rfl⟩

theorem mem_barOf_of_le {X : Subgroup G} (hKX : kerV N z ≤ X) {n : N} :
    piK N z n ∈ barOf N z X ↔ (n : G) ∈ X := by
  constructor
  · rintro ⟨x, hx, hxn⟩
    rw [piK_eq_iff] at hxn
    have := X.mul_mem (mem_subgroupOf.1 hx) (hKX hxn)
    simpa using this
  · exact piK_mem_barOf

theorem mem_Mb {n : N} : piK N z n ∈ barOf N z (cenM N z) ↔ (n : G) ∈ cenM N z :=
  mem_barOf_of_le Hyp.kerV_le_M

namespace Hyp

variable {U P : Subgroup G} (h : Hyp N U P z)
include h

theorem sq_mem_kerV [Finite G] {q : G} (hq : q ∈ U ⊔ P) : q * q ∈ kerV N z := by
  obtain ⟨u, hu, p, hp, rfl⟩ := h.mem_sup.1 hq
  have hupu : u * p * (u * p) = p * p := by
    calc u * p * (u * p) = u * (p * u) * p := by group
      _ = u * (u * p) * p := by rw [h.Ucen u hu p (h.PN hp)]
      _ = (u * u) * (p * p) := by group
      _ = p * p := by rw [h.Usq u hu, one_mul]
  rw [hupu]
  have hc := CFSG.RankThree.Literature.FSmith.sq_mem_center h.ext (⟨p, hp⟩ : P)
  rcases h.ZP (p * p) (P.mul_mem hp hp) (fun y hy => by
      have := mem_center_iff.1 hc ⟨y, hy⟩
      have := congrArg Subtype.val this
      simpa [pow_two] using this.symm) with h1 | h1
  · rw [h1]
    exact (kerV N z).one_mem
  · rw [h1]
    exact h.z_mem_kerV

theorem commutator_mem_kerV [Finite G] {q q' : G} (hq : q ∈ U ⊔ P) (hq' : q' ∈ U ⊔ P) :
    q * q' * q⁻¹ * q'⁻¹ ∈ kerV N z := by
  obtain ⟨u, hu, p, hp, rfl⟩ := h.mem_sup.1 hq
  obtain ⟨u', hu', p', hp', rfl⟩ := h.mem_sup.1 hq'
  have hpN := h.PN hp
  have hp'N := h.PN hp'
  have h1 : u * p * (u' * p') * (u * p)⁻¹ * (u' * p')⁻¹ = p * p' * p⁻¹ * p'⁻¹ := by
    have e1 : u * (p * (u' * p') * p⁻¹) = (p * (u' * p') * p⁻¹) * u :=
      h.Ucen u hu _ (N.mul_mem (N.mul_mem hpN (N.mul_mem (h.UN hu') hp'N)) (N.inv_mem hpN))
    have e2 : u' * (p * p' * p⁻¹ * p'⁻¹) = (p * p' * p⁻¹ * p'⁻¹) * u' :=
      h.Ucen u' hu' _ (N.mul_mem (N.mul_mem (N.mul_mem hpN hp'N) (N.inv_mem hpN))
        (N.inv_mem hp'N))
    have e3 : u' * p⁻¹ = p⁻¹ * u' := h.Ucen u' hu' _ (N.inv_mem hpN)
    calc u * p * (u' * p') * (u * p)⁻¹ * (u' * p')⁻¹
        = u * (p * (u' * p') * p⁻¹) * u⁻¹ * (u' * p')⁻¹ := by group
      _ = (p * (u' * p') * p⁻¹) * u * u⁻¹ * (u' * p')⁻¹ := by rw [e1]
      _ = p * u' * p' * p⁻¹ * p'⁻¹ * u'⁻¹ := by group
      _ = p * (u' * p') * p⁻¹ * p'⁻¹ * u'⁻¹ := by group
      _ = p * (p' * u') * p⁻¹ * p'⁻¹ * u'⁻¹ := by rw [h.Ucen u' hu' p' hp'N]
      _ = p * p' * (u' * p⁻¹) * p'⁻¹ * u'⁻¹ := by group
      _ = p * p' * (p⁻¹ * u') * p'⁻¹ * u'⁻¹ := by rw [e3]
      _ = p * p' * p⁻¹ * (u' * p'⁻¹) * u'⁻¹ := by group
      _ = p * p' * p⁻¹ * (p'⁻¹ * u') * u'⁻¹ := by rw [h.Ucen u' hu' _ (N.inv_mem hp'N)]
      _ = p * p' * p⁻¹ * p'⁻¹ := by group
  rw [h1]
  have hc := CFSG.RankThree.Literature.FSmith.commutatorElement_mem_center h.ext
    (⟨p, hp⟩ : P) ⟨p', hp'⟩
  have hmem : p * p' * p⁻¹ * p'⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem hp hp') (P.inv_mem hp)) (P.inv_mem hp')
  rcases h.ZP _ hmem (fun y hy => by
      have := mem_center_iff.1 hc ⟨y, hy⟩
      have := congrArg Subtype.val this
      simpa [commutatorElement_def] using this.symm) with h2 | h2
  · rw [h2]
    exact (kerV N z).one_mem
  · rw [h2]
    exact h.z_mem_kerV

theorem sqQb [Finite G] {x : Gbar N z} (hx : x ∈ barOf N z (U ⊔ P)) : x * x = 1 := by
  obtain ⟨n, hn, rfl⟩ := hx
  rw [← map_mul, piK_eq_one]
  exact h.sq_mem_kerV (mem_subgroupOf.1 hn)

theorem commQb [Finite G] {x y : Gbar N z} (hx : x ∈ barOf N z (U ⊔ P))
    (hy : y ∈ barOf N z (U ⊔ P)) : x * y = y * x := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨m, hm, rfl⟩ := hy
  have hc : piK N z (n * m * n⁻¹ * m⁻¹) = 1 := by
    rw [piK_eq_one]
    simpa using h.commutator_mem_kerV (mem_subgroupOf.1 hn) (mem_subgroupOf.1 hm)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hc
  calc piK N z n * piK N z m
      = piK N z n * piK N z m * (piK N z n)⁻¹ * (piK N z m)⁻¹ * (piK N z m * piK N z n) := by
        group
    _ = piK N z m * piK N z n := by rw [hc, one_mul]

omit h in
theorem eq_bot_of_normal_le {Y : Subgroup (Gbar N z)} (hY : Y.Normal)
    (hYM : Y ≤ barOf N z (cenM N z)) : Y = ⊥ := by
  set Y' : Subgroup G := (Y.comap (piK N z)).map N.subtype with hY'
  have hY'M : Y' ≤ cenM N z := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_Mb.1 (hYM (mem_comap.1 hn))
  have hY'n : ∀ m ∈ N, ∀ x ∈ Y', m * x * m⁻¹ ∈ Y' := by
    rintro m hm _ ⟨n, hn, rfl⟩
    refine ⟨⟨m, hm⟩ * n * ⟨m, hm⟩⁻¹, mem_comap.2 ?_, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact hY.conj_mem _ (mem_comap.1 hn) _
  have hle := Hyp.le_kerV hY'M hY'n
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := piK_surjective y
  rw [mem_bot, piK_eq_one]
  exact hle ⟨n, mem_comap.2 hy, rfl⟩

theorem o2 [Finite G] {Y : Subgroup (Gbar N z)} (hY : Y.Normal) (hY2 : IsPGroup 2 Y) : Y = ⊥ := by
  apply eq_bot_of_normal_le hY
  obtain ⟨T, hT⟩ := h.syl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Y ≤ ((Sylow.mapSurjective piK_surjective T : Sylow 2 (Gbar N z)) :
      Subgroup (Gbar N z)) := IsPGroup.le_sylow_of_normal hY2 _
  intro y hy
  have hy' := hle hy
  rw [Sylow.coe_mapSurjective] at hy'
  obtain ⟨t, ht, rfl⟩ := hy'
  exact piK_mem_barOf (mem_inf.2 ⟨t.2, mem_centralizer_singleton_iff.2 (hT t ht)⟩)

theorem le_Mb [Finite G] {H : Subgroup (Gbar N z)} (hQH : barOf N z (U ⊔ P) ≤ H) (hH : H ≠ ⊤) :
    H ≤ barOf N z (cenM N z) := by
  set H' : Subgroup G := (H.comap (piK N z)).map N.subtype with hH'
  have hQH' : U ⊔ P ≤ H' := fun q hq =>
    ⟨⟨q, h.sup_le_N hq⟩, mem_comap.2 (hQH (piK_mem_barOf hq)), rfl⟩
  have hne : H' ≠ N := by
    intro he
    apply hH
    rw [eq_top_iff]
    intro x _
    obtain ⟨n, rfl⟩ := piK_surjective x
    have hn : (n : G) ∈ H' := by rw [he]; exact n.2
    obtain ⟨m, hm, hmn⟩ := hn
    have hmn' : m = n := Subtype.ext hmn
    exact hmn' ▸ mem_comap.1 hm
  have hle := h.max H' hQH' (map_subtype_le _) hne
  intro x hx
  obtain ⟨n, rfl⟩ := piK_surjective x
  exact mem_Mb.2 (mem_inf.2 ⟨n.2, hle ⟨n, mem_comap.2 hx, rfl⟩⟩)

theorem cent_le [Finite G] {x : Gbar N z} (hx : x ∈ barOf N z (U ⊔ P)) (hx1 : x ≠ 1) :
    centralizer ({x} : Set (Gbar N z)) ≤ barOf N z (cenM N z) := by
  apply h.le_Mb
  · intro q hq
    rw [mem_centralizer_singleton_iff]
    exact h.commQb hq hx
  · intro htop
    apply hx1
    have hcen : x ∈ center (Gbar N z) := mem_center_iff.2 fun y =>
      mem_centralizer_singleton_iff.1 (htop ▸ mem_top y)
    have hZ : (zpowers x).Normal := normal_of_le_center (zpowers_le.2 hcen)
    have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two, h.sqQb hx]) hx1
    have hZ2 : IsPGroup 2 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    exact zpowers_eq_bot.1 (h.o2 hZ hZ2)

theorem ti [Finite G] (g : Gbar N z) {x : Gbar N z} (hx : x ∈ barOf N z (U ⊔ P)) (hx1 : x ≠ 1)
    (hgx : g * x * g⁻¹ ∈ barOf N z (U ⊔ P)) : g ∈ barOf N z (cenM N z) := by
  obtain ⟨g', rfl⟩ := piK_surjective g
  have hgx1 : piK N z g' * x * (piK N z g')⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    calc x = (piK N z g')⁻¹ * (piK N z g' * x * (piK N z g')⁻¹) * piK N z g' := by group
      _ = 1 := by rw [h1]; group
  have hcent := h.cent_le hgx hgx1
  apply mem_Mb.2
  apply h.mem_M_of_conj_le g'.2
  intro q hq
  have hqN := h.sup_le_N hq
  have hmem : piK N z (g' * ⟨q, hqN⟩ * g'⁻¹) ∈ barOf N z (cenM N z) := by
    apply hcent
    rw [mem_centralizer_singleton_iff, map_mul, map_mul, map_inv]
    have hc := h.commQb (piK_mem_barOf (n := ⟨q, hqN⟩) hq) hx
    calc piK N z g' * piK N z ⟨q, hqN⟩ * (piK N z g')⁻¹ * (piK N z g' * x * (piK N z g')⁻¹)
        = piK N z g' * (piK N z ⟨q, hqN⟩ * x) * (piK N z g')⁻¹ := by group
      _ = piK N z g' * (x * piK N z ⟨q, hqN⟩) * (piK N z g')⁻¹ := by rw [hc]
      _ = piK N z g' * x * (piK N z g')⁻¹ *
          (piK N z g' * piK N z ⟨q, hqN⟩ * (piK N z g')⁻¹) := by group
  simpa using mem_Mb.1 hmem

theorem gen_bar [Finite G] {g : Gbar N z} (hg : g ∉ barOf N z (cenM N z)) :
    barOf N z (U ⊔ P) ⊔ (barOf N z (U ⊔ P)).map (MulAut.conj g).toMonoidHom = ⊤ := by
  by_contra hne
  apply hg
  obtain ⟨g', rfl⟩ := piK_surjective g
  have hle := h.le_Mb le_sup_left hne
  apply mem_Mb.2
  apply h.mem_M_of_conj_le g'.2
  intro q hq
  have hmem : piK N z (g' * ⟨q, h.sup_le_N hq⟩ * g'⁻¹) ∈ barOf N z (cenM N z) := by
    apply hle
    apply mem_sup_right
    rw [mem_map_conj]
    simpa [mul_assoc] using piK_mem_barOf (N := N) (z := z) (n := ⟨q, h.sup_le_N hq⟩) hq
  simpa using mem_Mb.1 hmem

theorem Qb_ne_bot [Finite G] : barOf N z (U ⊔ P) ≠ ⊥ := by
  intro hQ
  have hQK : U ⊔ P ≤ kerV N z := fun q hq => by
    have := piK_mem_barOf (N := N) (z := z) (n := ⟨q, h.sup_le_N hq⟩) hq
    rw [hQ, mem_bot, piK_eq_one] at this
    exact this
  obtain ⟨g, hgN, hgz⟩ : ∃ g ∈ N, g ∉ centralizer ({z} : Set G) := by
    by_contra hcon
    push Not at hcon
    exact h.notcen hcon
  have hgM : g ∉ cenM N z := fun hg => hgz (mem_inf.1 hg).2
  apply h.notcen
  refine (h.le_sup_conj hgN hgM).trans
    (le_trans ?_ ((kerV_le_M (N := N) (z := z)).trans inf_le_right))
  refine sup_le hQK ?_
  rintro _ ⟨q, hq, rfl⟩
  exact kerV_normalized hgN (hQK hq)

theorem Mb_ne_top : barOf N z (cenM N z) ≠ ⊤ := by
  intro htop
  apply h.notcen
  intro n hn
  have := mem_Mb.1 (htop ▸ mem_top (piK N z ⟨n, hn⟩))
  exact (mem_inf.1 this).2

theorem absTI [Finite G] : AbsTI (Gbar N z) (barOf N z (U ⊔ P)) (barOf N z (cenM N z)) where
  sq := fun _ hx => h.sqQb hx
  comm := fun _ hx _ hy => h.commQb hx hy
  QM := by
    rintro _ ⟨n, hn, rfl⟩
    exact piK_mem_barOf (h.sup_le_M (mem_subgroupOf.1 hn))
  norm := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    have hmM := mem_subgroupOf.1 hm
    have := h.Qnorm m (mem_inf.1 hmM).1 (mem_centralizer_singleton_iff.1 (mem_inf.1 hmM).2) q
      (mem_subgroupOf.1 hq)
    exact piK_mem_barOf (by simpa using this)
  cent := fun _ hx hx1 => h.cent_le hx hx1
  ti := fun g _ hx hx1 hgx => h.ti g hx hx1 hgx
  gen := fun _ hg => h.gen_bar hg
  o2 := fun _ hY hY2 => h.o2 hY hY2

theorem normalClosure_Qb [Finite G] :
    normalClosure (barOf N z (U ⊔ P) : Set (Gbar N z)) = ⊤ := by
  by_contra hne
  have hle := h.le_Mb le_normalClosure hne
  have hbot := eq_bot_of_normal_le inferInstance hle
  exact h.Qb_ne_bot (eq_bot_iff.2 (le_normalClosure.trans hbot.le))

theorem card_Qb_mul [Finite G] : Nat.card (barOf N z (U ⊔ P)) *
    Nat.card ↥((U ⊔ P) ⊓ kerV N z) = Nat.card ↥(U ⊔ P) := by
  set Q' := (U ⊔ P).subgroupOf N with hQ'def
  let f : ↥Q' →* Gbar N z := (piK N z).comp Q'.subtype
  have hrange : f.range = barOf N z (U ⊔ P) := by
    rw [MonoidHom.range_comp, range_subtype]
  have h1 := card_mul_index f.ker
  rw [index_ker, hrange] at h1
  have hQ' : Nat.card Q' = Nat.card ↥(U ⊔ P) :=
    Nat.card_congr (subgroupOfEquivOfLe h.sup_le_N).toEquiv
  have hker : Nat.card f.ker = Nat.card ↥((U ⊔ P) ⊓ kerV N z) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(((x : Q') : N) : G), mem_inf.2 ⟨mem_subgroupOf.1 (x : Q').2,
          piK_eq_one.1 (MonoidHom.mem_ker.1 x.2)⟩⟩
        invFun := fun y => ⟨⟨⟨y, h.sup_le_N (mem_inf.1 y.2).1⟩,
          mem_subgroupOf.2 (mem_inf.1 y.2).1⟩, MonoidHom.mem_ker.2 (piK_eq_one.2 (mem_inf.1 y.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hker, hQ'] at h1
  rw [mul_comm]
  exact h1

theorem exists_sylow [Finite G] : ∃ T : Sylow 2 (Gbar N z),
    barOf N z (U ⊔ P) ≤ T ∧ (T : Subgroup (Gbar N z)) ≤ barOf N z (cenM N z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := h.syl
  set Q' := (U ⊔ P).subgroupOf N with hQ'def
  have hQ'2 : IsPGroup 2 Q' := h.isPGroup_sup.comap_of_injective N.subtype N.subtype_injective
  have hTM : ∀ t ∈ (T : Subgroup N), (t : G) ∈ cenM N z := fun t ht =>
    mem_inf.2 ⟨t.2, mem_centralizer_singleton_iff.2 (hT t ht)⟩
  have hTnorm : (T : Subgroup N) ≤ normalizer (Q' : Set N) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    have htM := hTM t ht
    have htz := mem_centralizer_singleton_iff.1 (mem_inf.1 htM).2
    have htz' : (t : G)⁻¹ * z = z * (t : G)⁻¹ := by
      calc (t : G)⁻¹ * z = (t : G)⁻¹ * (z * t) * (t : G)⁻¹ := by group
        _ = (t : G)⁻¹ * (t * z) * (t : G)⁻¹ := by rw [htz]
        _ = z * (t : G)⁻¹ := by group
    constructor
    · intro hx
      rw [hQ'def, mem_subgroupOf] at hx ⊢
      simpa using h.Qnorm t t.2 htz x hx
    · intro hx
      rw [hQ'def, mem_subgroupOf] at hx ⊢
      have := h.Qnorm (t : G)⁻¹ (N.inv_mem t.2) htz' _ hx
      simpa [mul_assoc] using this
  have hsup := IsPGroup.to_sup_of_normal_right' T.isPGroup' hQ'2 hTnorm
  have hQT : Q' ≤ T := by
    rw [← T.is_maximal' hsup le_sup_left]
    exact le_sup_right
  refine ⟨Sylow.mapSurjective piK_surjective T, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    exact map_mono hQT
  · rw [Sylow.coe_mapSurjective]
    rintro _ ⟨t, ht, rfl⟩
    exact piK_mem_barOf (hTM t ht)

end Hyp

end CFSG.LargeExtraspecial.Asc22
