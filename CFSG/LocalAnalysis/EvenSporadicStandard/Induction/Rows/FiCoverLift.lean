module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction.Cover

open Subgroup CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {X : Type} [Group X]

theorem commutator_eq_self_of_isPerfect {K : Subgroup X} (h : Group.IsPerfect ↥K) : ⁅K, K⁆ = K := by
  have h1 : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
    have := Group.isPerfect_def.1 h
    rwa [_root_.commutator_def] at this
  have h2 := congrArg (Subgroup.map K.subtype) h1
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2
  exact h2

theorem mem_centralizer_singleton_iff_coe (hodd : Odd (Nat.card (center X))) {u x : X}
    (hu : u * u = 1) :
    x ∈ centralizer ({u} : Set X) ↔
      (x : X ⧸ center X) ∈ centralizer ({(u : X ⧸ center X)} : Set (X ⧸ center X)) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  · intro h
    have hxu : x * u * x⁻¹ * (x * u * x⁻¹) = 1 := by
      calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
        _ = 1 := by rw [hu]; group
    have hmk : ((x * u * x⁻¹ : X) : X ⧸ center X) = (u : X ⧸ center X) := by
      have h' : (x : X ⧸ center X) * (u : X ⧸ center X) =
          (u : X ⧸ center X) * (x : X ⧸ center X) := h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h']
      group
    have := Closing.eq_of_mk_eq_of_sq hodd hxu hu hmk
    calc x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [this]

theorem centralizer_singleton_eq_sup [Finite X] (hodd : Odd (Nat.card (center X))) {u : X}
    (hu : u * u = 1) {K : Subgroup X} (hKu : ∀ k ∈ K, k * u = u * k)
    (hbar : bar K = centralizer ({(u : X ⧸ center X)} : Set (X ⧸ center X))) :
    centralizer ({u} : Set X) = K ⊔ center X := by
  apply le_antisymm
  · intro x hx
    have h1 := (mem_centralizer_singleton_iff_coe hodd hu).1 hx
    rw [← hbar] at h1
    obtain ⟨k, hk, z, hz, rfl⟩ := mem_bar_iff_exists_mem_mul.1 h1
    exact (mem_sup_central le_rfl).2 ⟨k, hk, z, hz, rfl⟩
  · refine sup_le (fun k hk => mem_centralizer_singleton_iff.2 (hKu k hk)) ?_
    intro z hz
    exact mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 hz u).symm

theorem mem_centralizer_of_mk_mem {K : Subgroup X} (hK : ⁅K, K⁆ = K) {x : X}
    (hx : (x : X ⧸ center X) ∈ centralizer (bar K : Set (X ⧸ center X))) :
    x ∈ centralizer (K : Set X) := by
  have hZ : ⁅center X, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact Subgroup.mem_center_iff.1 hz g
  have hcen : ∀ k ∈ K, ∀ n : ℤ, ⁅k, x ^ n⁆ ∈ center X := by
    intro k hk n
    have h1 : ((x ^ n : X) : X ⧸ center X) ∈ centralizer (bar K : Set (X ⧸ center X)) := by
      rw [QuotientGroup.mk_zpow]
      exact zpow_mem hx n
    rw [← QuotientGroup.eq_one_iff]
    show (QuotientGroup.mk' (center X)) ⁅k, x ^ n⁆ = 1
    rw [map_commutatorElement]
    simp only [QuotientGroup.mk'_apply]
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.1 h1 _ (mk_mem_bar_of_mem hk)
  have hM : ⁅K, zpowers x⁆ ≤ center X :=
    Subgroup.commutator_le.2 fun k hk g hg => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact hcen k hk n
  have h1 : ⁅⁅K, zpowers x⁆, K⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono hM le_rfl).trans hZ.le)
  have h2 : ⁅⁅zpowers x, K⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (zpowers x) K]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K)
    (H₃ := zpowers x) h1 h2
  rw [hK] at h3
  have h4 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.1 (h4 hk) x (Subgroup.mem_zpowers x)).symm

theorem centralizer_eq_comap {K : Subgroup X} (hK : ⁅K, K⁆ = K) :
    centralizer (K : Set X) =
      (centralizer (bar K : Set (X ⧸ center X))).comap (QuotientGroup.mk' (center X)) := by
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hx k hk
    simp only [QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  · intro hx
    exact mem_centralizer_of_mk_mem hK hx


theorem map_map_conj (K : Subgroup X) (g : X) :
    (K.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' (center X)) =
      (bar K).map (MulAut.conj (g : X ⧸ center X)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_conj_le_of_mk_mem_normalizer {K : Subgroup X} (hK : ⁅K, K⁆ = K) {g : X}
    (hg : (g : X ⧸ center X) ∈ normalizer (bar K : Set (X ⧸ center X))) :
    K.map (MulAut.conj g).toMonoidHom ≤ K := by
  have hP : ⁅K.map (MulAut.conj g).toMonoidHom, K.map (MulAut.conj g).toMonoidHom⁆ =
      K.map (MulAut.conj g).toMonoidHom := by
    rw [← Subgroup.map_commutator, hK]
  refine le_of_perfect_le_sup_central (Z' := center X) le_rfl hP ?_
  rintro _ ⟨k, hk, rfl⟩
  have hmk : ((g * k * g⁻¹ : X) : X ⧸ center X) ∈ bar K := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact (Subgroup.mem_normalizer_iff.1 hg _).1 (mk_mem_bar_of_mem hk)
  obtain ⟨k', hk', z, hz, hx⟩ := mem_bar_iff_exists_mem_mul.1 hmk
  exact (mem_sup_central le_rfl).2 ⟨k', hk', z, hz, hx.symm⟩

theorem mem_normalizer_of_mk_mem {K : Subgroup X} (hK : ⁅K, K⁆ = K) {g : X}
    (hg : (g : X ⧸ center X) ∈ normalizer (bar K : Set (X ⧸ center X))) :
    g ∈ normalizer (K : Set X) := by
  have h1 := map_conj_le_of_mk_mem_normalizer hK hg
  have hg' : ((g⁻¹ : X) : X ⧸ center X) ∈ normalizer (bar K : Set (X ⧸ center X)) := by
    rw [QuotientGroup.mk_inv]
    exact Subgroup.inv_mem _ hg
  have h2 := map_conj_le_of_mk_mem_normalizer hK hg'
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact h1 ⟨h, hh, by simp [MulAut.conj_apply]⟩
  · intro hh
    have hx : (MulAut.conj g⁻¹).toMonoidHom (g * h * g⁻¹) ∈
        K.map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hh
    have := h2 hx
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem card_comap_mk [Finite X] (D : Subgroup (X ⧸ center X)) :
    Nat.card (D.comap (QuotientGroup.mk' (center X))) =
      Nat.card (center X) * Nat.card D := by
  set D' := D.comap (QuotientGroup.mk' (center X)) with hD'
  have hbar : bar D' = D := Subgroup.map_comap_eq_self_of_surjective QuotientGroup.mk_surjective D
  have hle : center X ≤ D' := fun z hz => by
    rw [hD', Subgroup.mem_comap]
    simp [(QuotientGroup.eq_one_iff z).2 hz]
  have h := card_mul_bar D'
  rw [hbar] at h
  rw [← h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem stdBare_of_bar [Finite X] (hodd : Odd (Nat.card (center X))) {K : Subgroup X}
    (hK : ⁅K, K⁆ = K) (h : StdBare (bar K)) : StdBare K := by
  refine ⟨fun g hbot => ?_, fun g hg => ?_⟩
  · apply h.1 (g : X ⧸ center X)
    have := congrArg (Subgroup.map (QuotientGroup.mk' (center X))) hbot
    rw [Subgroup.map_commutator, map_map_conj, Subgroup.map_bot] at this
    exact this
  · have hg' : (g : X ⧸ center X) ∉ normalizer (bar K : Set (X ⧸ center X)) := fun hn =>
      hg (mem_normalizer_of_mk_mem hK hn)
    have hodd' := h.2 _ hg'
    set C := centralizer (bar K : Set (X ⧸ center X)) with hC
    have hCX : centralizer (K : Set X) = C.comap (QuotientGroup.mk' (center X)) :=
      centralizer_eq_comap hK
    have hmap : (centralizer (K : Set X)).map (MulAut.conj g).toMonoidHom =
        (C.map (MulAut.conj (g : X ⧸ center X)).toMonoidHom).comap
          (QuotientGroup.mk' (center X)) := by
      ext x
      rw [hCX, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨QuotientGroup.mk' (center X) y, hy, ?_⟩
        simp [MulAut.conj_apply]
      · rintro ⟨c, hc, hcx⟩
        refine ⟨g⁻¹ * x * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
        have : (QuotientGroup.mk' (center X)) (g⁻¹ * x * g) = c := by
          rw [map_mul, map_mul, map_inv, ← hcx]
          simp only [QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [Subgroup.mem_comap, this]
        exact hc
    rw [hmap, hCX, ← Subgroup.comap_inf, card_comap_mk]
    exact hodd.mul hodd'


theorem eq_one_of_mem_center_of_isPGroup [Finite X] (hodd : Odd (Nat.card (center X)))
    {S : Subgroup X} (hS : IsPGroup 2 S) {s : X} (hs : s ∈ S) (hz : s ∈ center X) : s = 1 := by
  obtain ⟨n, hn⟩ := hS ⟨s, hs⟩
  have h1 : s ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h2 : orderOf s ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf s ∣ Nat.card (center X) := Subgroup.orderOf_dvd_natCard (center X) hz
  have hcop : Nat.Coprime (Nat.card (center X)) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hodd)
  have h4 : orderOf s = 1 := Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h3 h2)
  exact orderOf_eq_one_iff.1 h4

theorem eq_of_mk_eq_of_mem_isPGroup [Finite X] (hodd : Odd (Nat.card (center X)))
    {S : Subgroup X} (hS : IsPGroup 2 S) {a b : X} (ha : a ∈ S) (hb : b ∈ S)
    (h : (a : X ⧸ center X) = b) : a = b := by
  have h1 : a⁻¹ * b ∈ center X := QuotientGroup.eq.1 h
  have h2 : a⁻¹ * b = 1 :=
    eq_one_of_mem_center_of_isPGroup hodd hS (S.mul_mem (S.inv_mem ha) hb) h1
  rwa [inv_mul_eq_one] at h2

theorem exists_squareFacts_of_bar [Finite X] (hodd : Odd (Nat.card (center X)))
    {K : Subgroup X} {u : X} (hu : u * u = 1) (hKu : ∀ k ∈ K, k * u = u * k)
    {Sb : Subgroup (X ⧸ center X)} {db : X ⧸ center X}
    (hSq : SquareFacts (bar K) Sb (u : X ⧸ center X) db) :
    ∃ (S : Subgroup X) (d : X), SquareFacts K S u d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup X := K ⊓ Sb.comap (QuotientGroup.mk' (center X)) with hP
  obtain ⟨Q⟩ : Nonempty (Sylow 2 P) := inferInstance
  set S : Subgroup X := (Q : Subgroup P).map P.subtype with hS
  have hSP : S ≤ P := Subgroup.map_subtype_le _
  have hSK : S ≤ K := hSP.trans inf_le_left
  have hSp : IsPGroup 2 S := Q.isPGroup'.map P.subtype
  have hbarP : bar P = Sb := by
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact hp.2
    · intro y hy
      obtain ⟨k, hk, rfl⟩ := mem_bar.1 (hSq.S_le hy)
      exact ⟨k, ⟨hk, hy⟩, rfl⟩
  have hSb : Nat.card Sb = 2 ^ (Nat.card K).factorization 2 := by
    rw [hSq.S_card]
    congr 1
    exact twoAdic_bar hodd K
  have hSbcard : (Nat.card Sb).factorization 2 = (Nat.card K).factorization 2 := by
    rw [hSb, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hPtwo : (Nat.card P).factorization 2 = (Nat.card K).factorization 2 := by
    have := twoAdic_bar hodd P
    rw [hbarP] at this
    unfold twoAdic at this
    rw [← this]
    exact hSbcard
  have hScard : Nat.card S = 2 ^ (Nat.card K).factorization 2 := by
    rw [hS, Subgroup.card_map_of_injective P.subtype_injective, Q.card_eq_multiplicity, hPtwo]
  have hZS : (center X).subgroupOf S = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_mem_center_of_isPGroup hodd hSp s.2 hs)
  have hbarS : bar S = Sb := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact hbarP ▸ Subgroup.map_mono hSP
    · have h := card_mul_bar S
      rw [hZS, Subgroup.card_bot, one_mul] at h
      rw [h, hScard, hSb]
  have hmkS : ∀ s ∈ S, (s : X ⧸ center X) ∈ Sb := fun s hs => hbarS ▸ mk_mem_bar_of_mem hs
  have hlift : ∀ y ∈ Sb, ∃ s ∈ S, (s : X ⧸ center X) = y := fun y hy =>
    mem_bar.1 (hbarS ▸ hy)
  have hinj : ∀ a ∈ S, ∀ b ∈ S, (a : X ⧸ center X) = b → a = b := fun a ha b hb h =>
    eq_of_mk_eq_of_mem_isPGroup hodd hSp ha hb h
  have hubS : (u : X ⧸ center X) ∈ Sb :=
    mem_of_commute_sylow hSq.S_le hSq.S_card hSq.u_mem hSq.u_sq
      (fun q hq => hSq.u_central q (hSq.S_le hq))
  have hdbS : db ∈ Sb :=
    mem_of_commute_sylow hSq.S_le hSq.S_card hSq.d_mem hSq.d_sq hSq.d_comm
  have hbu : (u : X ⧸ center X) * (u : X ⧸ center X) = 1 := hSq.u_sq
  have hbd : db * db = 1 := hSq.d_sq
  obtain ⟨u', hu'S, hu'⟩ := hlift _ hubS
  have hu'sq : u' * u' = 1 := by
    have h2 : ((u' * u' : X) : X ⧸ center X) = ((1 : X) : X ⧸ center X) := by
      rw [QuotientGroup.mk_mul, hu', hbu, QuotientGroup.mk_one]
    exact hinj _ (S.mul_mem hu'S hu'S) 1 S.one_mem h2
  have huu' : u' = u := Closing.eq_of_mk_eq_of_sq hodd hu'sq hu hu'
  have huS : u ∈ S := huu' ▸ hu'S
  obtain ⟨d, hdS, hd⟩ := hlift _ hdbS
  have hdsq : d * d = 1 := by
    have h2 : ((d * d : X) : X ⧸ center X) = ((1 : X) : X ⧸ center X) := by
      rw [QuotientGroup.mk_mul, hd, hbd, QuotientGroup.mk_one]
    exact hinj _ (S.mul_mem hdS hdS) 1 S.one_mem h2
  have hud : u * d = d * u := (hKu d (hSK hdS)).symm
  have hudsq : (u * d) * (u * d) = 1 := by
    calc (u * d) * (u * d) = u * (d * u) * d := by group
      _ = u * (u * d) * d := by rw [← hud]
      _ = (u * u) * (d * d) := by group
      _ = 1 := by rw [hu, hdsq, one_mul]
  refine ⟨S, d, ?_⟩
  exact
  { S_le := hSK
    S_card := hScard
    d_mem := hSK hdS
    d_sq := hdsq
    d_ne_one := fun h => hSq.d_ne_one (by rw [← hd, h, QuotientGroup.mk_one])
    d_ne_u := fun h => hSq.d_ne_u (by rw [← hd, h])
    d_comm := fun s hs => by
      have e1 : s * d * s⁻¹ * (s * d * s⁻¹) = 1 := by
        calc s * d * s⁻¹ * (s * d * s⁻¹) = s * (d * d) * s⁻¹ := by group
          _ = 1 := by rw [hdsq]; group
      have e2 : ((s * d * s⁻¹ : X) : X ⧸ center X) = ((d : X) : X ⧸ center X) := by
        have := hSq.d_comm _ (hmkS s hs)
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hd, this]
        group
      have := Closing.eq_of_mk_eq_of_sq hodd e1 hdsq e2
      calc s * d = (s * d * s⁻¹) * s := by group
        _ = d * s := by rw [this]
    center_inv := fun s hs hss hsc => by
      have hss' : (s : X ⧸ center X) * (s : X ⧸ center X) = 1 := by
        rw [← QuotientGroup.mk_mul, hss, QuotientGroup.mk_one]
      have hsc' : ∀ x ∈ Sb, (s : X ⧸ center X) * x = x * (s : X ⧸ center X) := by
        intro x hx
        obtain ⟨y, hyS, rfl⟩ := hlift x hx
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hsc y hyS]
      rcases hSq.center_inv _ (hmkS s hs) hss' hsc' with h | h | h | h
      · left
        exact Closing.eq_of_mk_eq_of_sq hodd hss (mul_one 1) (h.trans (QuotientGroup.mk_one _).symm)
      · right; left
        exact Closing.eq_of_mk_eq_of_sq hodd hss hu h
      · right; right; left
        exact Closing.eq_of_mk_eq_of_sq hodd hss hdsq (h.trans hd.symm)
      · right; right; right
        refine Closing.eq_of_mk_eq_of_sq hodd hss hudsq ?_
        rw [h, QuotientGroup.mk_mul, hd]
    d_nonsq := fun s hs h => hSq.d_nonsq _ (hmkS s hs) (by rw [← QuotientGroup.mk_mul, h, hd])
    ud_sq := by
      obtain ⟨sb, hsb, hsbsq⟩ := hSq.ud_sq
      obtain ⟨s, hsS, hs⟩ := hlift sb hsb
      refine ⟨s, hsS, hinj _ (S.mul_mem hsS hsS) _ (S.mul_mem huS hdS) ?_⟩
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hs, hd, hsbsq]
    u_mem := mem_of_mk_mem hodd hu hSq.u_mem
    u_central := hKu
    u_sq := hu
    central_inv := fun z hz hzz hzc => by
      have hzz' : (z : X ⧸ center X) * (z : X ⧸ center X) = 1 := by
        rw [← QuotientGroup.mk_mul, hzz, QuotientGroup.mk_one]
      have hzc' : ∀ y ∈ bar K, (z : X ⧸ center X) * y = y * (z : X ⧸ center X) := by
        intro y hy
        obtain ⟨k, hk, rfl⟩ := mem_bar.1 hy
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hzc k hk]
      rcases hSq.central_inv _ (mk_mem_bar_of_mem hz) hzz' hzc' with h | h
      · left
        exact Closing.eq_of_mk_eq_of_sq hodd hzz (mul_one 1) (h.trans (QuotientGroup.mk_one _).symm)
      · right
        exact Closing.eq_of_mk_eq_of_sq hodd hzz hu h }


end CFSG.EvenSporadicStandard.Induction.Cover
