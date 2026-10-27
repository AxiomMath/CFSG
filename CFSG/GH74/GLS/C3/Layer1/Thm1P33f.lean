module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P33d
public import CFSG.Quasithin.Background.BlueprintB2Thompson

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

section F

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem Env33.exists_g (E : Env33 x y K T V W f z) (hconj : IsConj z f) :
    ∃ g ∈ normalizer (V : Set G), g * f * g⁻¹ = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hhf : c⁻¹ * f * c⁻¹⁻¹ = z := by rw [← hc]; group
  have hVz : V ≤ centralizer ({z} : Set G) := fun v hv =>
    mem_centralizer_singleton_iff.2 (E.hzZ.2 v hv)
  set h : G := c⁻¹ with hh
  have hCz : centralizer ({z} : Set G) = (centralizer ({f} : Set G)).map (MulAut.conj h).toMonoidHom := by
    ext y
    constructor
    · intro hy
      have hy' : y * z = z * y := mem_centralizer_singleton_iff.1 hy
      refine ⟨h⁻¹ * y * h, ?_, by simp [MulAut.conj_apply]; group⟩
      refine mem_centralizer_singleton_iff.2 ?_
      rw [← hhf] at hy'
      calc h⁻¹ * y * h * f = h⁻¹ * (y * (h * f * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * f * h⁻¹) * y) * h := by rw [hy']
        _ = f * (h⁻¹ * y * h) := by group
    · rintro ⟨w, hw, rfl⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have hw' : w * f = f * w := mem_centralizer_singleton_iff.1 hw
      rw [← hhf]
      show h * w * h⁻¹ * (h * f * h⁻¹) = h * f * h⁻¹ * (h * w * h⁻¹)
      calc h * w * h⁻¹ * (h * f * h⁻¹) = h * (w * f) * h⁻¹ := by group
        _ = h * (f * w) * h⁻¹ := by rw [hw']
        _ = h * f * h⁻¹ * (h * w * h⁻¹) := by group
  have hcardCz : Nat.card ↥(centralizer ({z} : Set G)) = Nat.card ↥(centralizer ({f} : Set G)) := by
    rw [hCz, Subgroup.card_map_of_injective (MulAut.conj h).injective]
  have hVsyl : IsSylowOf 2 V (centralizer ({z} : Set G)) := by
    refine isSylowOf_of_card hVz ?_
    rw [E.cfg.sylowV.card_eq, hcardCz]
  set V' : Subgroup G := V.map (MulAut.conj h).toMonoidHom with hV'
  have hV'z : V' ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hCz]
    exact ⟨v, E.hVC hv, rfl⟩
  have hV'syl : IsSylowOf 2 V' (centralizer ({z} : Set G)) := by
    refine isSylowOf_of_card hV'z ?_
    rw [hV', Subgroup.card_map_of_injective (MulAut.conj h).injective, E.cfg.sylowV.card_eq, hcardCz]
  obtain ⟨k, hk, hkV⟩ := hVsyl.exists_mem_conj hV'syl
  refine ⟨k⁻¹ * h, Thm1L3.mem_normalizer_of_conj_le (fun v hv => ?_), ?_⟩
  · have h1 : h * v * h⁻¹ ∈ V' := ⟨v, hv, rfl⟩
    have h2 := (hkV _).1 h1
    have : (k⁻¹ * h) * v * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * v * h⁻¹) * k := by group
    rw [this]; exact h2
  · have hkz : k * z = z * k := (mem_centralizer_singleton_iff.1 hk)
    calc (k⁻¹ * h) * f * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * f * h⁻¹) * k := by group
      _ = k⁻¹ * z * k := by rw [hhf]
      _ = z := by
        calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
          _ = k⁻¹ * (k * z) := by rw [hkz]
          _ = z := by group

omit [Finite G] in
theorem omega1_conj_mem {V : Subgroup G} {g : G} (hg : g ∈ normalizer (V : Set G)) :
    ∀ q ∈ omega1 V, g⁻¹ * q * g ∈ omega1 V := by
  intro q hq
  unfold omega1 at hq ⊢
  induction hq using Subgroup.closure_induction with
  | mem u hu =>
    refine Subgroup.subset_closure ⟨(normalizer_conj_mem hg).2 u hu.1, ?_⟩
    calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
      _ = 1 := by rw [hu.2]; group
  | one => rw [mul_one, inv_mul_cancel]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    have : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
    rw [this]; exact mul_mem ha hb
  | inv a _ ha =>
    have : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
    rw [this]; exact inv_mem ha

theorem Env33.hP_le_omega1 (E : Env33 x y K T V W f z) : T ⊓ K ≤ omega1 V := by
  intro p hp
  obtain ⟨n, -, hdih⟩ := E.hdih
  obtain ⟨u, hu, w, hw, huu, hww, hpuw⟩ := Thm1.exists_mul_involutions_of_dihedral hdih p hp
  rw [hpuw]
  exact (omega1 V).mul_mem (Subgroup.subset_closure ⟨E.hPV hu, huu⟩)
    (Subgroup.subset_closure ⟨E.hPV hw, hww⟩)

theorem Env33.omega1_le_PD (E : Env33 x y K T V W f z) (hD4 : Nat.card ↥(secD K f V) = 4)
    (hxZ : x ∈ zCenter V) : omega1 V ≤ (T ⊓ K) ⊔ secD K f V := by
  unfold omega1
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨huV, huu⟩
  have hux : u * x = x * u := hxZ.2 u huV
  have := E.hOmega1S u huV hux huu
  show u ∈ (T ⊓ K) ⊔ secD K f V
  rwa [E.hDeq4 hD4]

theorem Env33.false_f_card4 (E : Env33 x y K T V W f z) (hD4 : Nat.card ↥(secD K f V) = 4) {g : G}
    (hgN : g ∈ normalizer (V : Set G)) (hgf : g * f * g⁻¹ = z) : False := by
  have hg : (secD K f V).map (MulAut.conj g).toMonoidHom ≠ secD K f V := fun h =>
    E.hzD (by rw [← h]; exact mem_map_conj.2 ⟨f, E.hfD, hgf⟩)
  have hxZ := E.key_d hD4 hgN hg
  obtain ⟨n, hn3, hdih⟩ := E.hdih
  obtain ⟨c, hcP, hcc⟩ := exists_sq_eq_of_dihedral hn3 hdih E.hzP E.hz1
    (fun q hq => (E.cfg.z_mem.2.2 q hq.1).symm)
  have hqΩ : g⁻¹ * c * g ∈ omega1 V := omega1_conj_mem hgN c (E.hP_le_omega1 hcP)
  obtain ⟨p, hp, d, hd, hqpd⟩ := Thm1P310.exists_mul_of_mem_sup (E.hPcD4 hD4)
    (E.omega1_le_PD hD4 hxZ hqΩ)
  have hdd : d * d = 1 := mul_self_eq_one_of_mem_klein E.hx2 E.hf2' E.cfg.hxf (E.hDeq4 hD4 ▸ hd)
  have hpd : p * d = d * p := E.hPcD4 hD4 p hp d hd
  have hf : f = (g⁻¹ * c * g) * (g⁻¹ * c * g) := by
    calc f = g⁻¹ * (g * f * g⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [hgf]
      _ = g⁻¹ * (c * c) * g := by rw [hcc]
      _ = (g⁻¹ * c * g) * (g⁻¹ * c * g) := by group
  have hfp : f = p * p := by
    rw [hf, hqpd]
    calc p * d * (p * d) = p * (d * p) * d := by group
      _ = p * (p * d) * d := by rw [← hpd]
      _ = p * p * (d * d) := by group
      _ = p * p := by rw [hdd, mul_one]
  have hfP : f ∈ T ⊓ K := by rw [hfp]; exact (T ⊓ K).mul_mem hp hp
  have : f ∈ (T ⊓ K) ⊓ secD K f V := ⟨hfP, E.hfD⟩
  rw [E.hPD, Subgroup.mem_bot] at this
  exact E.hf1 this

omit [Finite G] in
theorem elemAbelian_zpowers {u : G} (hu : u * u = 1) : IsElementaryAbelian 2 ↥(zpowers u) := by
  refine Back.isElementaryAbelian_of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self u i j).eq
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    rw [← zpow_add, ← two_mul, zpow_mul]
    have : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
    rw [this, one_zpow]

theorem elemAbelian_sup_of_commute {A B : Subgroup G} (hA : IsElementaryAbelian 2 ↥A)
    (hB : IsElementaryAbelian 2 ↥B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) :
    IsElementaryAbelian 2 ↥(A ⊔ B) ∧ Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥(A ⊔ B) := by
  obtain ⟨habA, hsqA⟩ := Back.forall_of_isElementaryAbelian hA
  obtain ⟨habB, hsqB⟩ := Back.forall_of_isElementaryAbelian hB
  refine ⟨Back.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_), ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hcomm hu
    obtain ⟨a', ha', b', hb', rfl⟩ := Thm1P310.exists_mul_of_mem_sup hcomm hv
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [habA a ha a' ha', habB b hb b' hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hcomm a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hcomm hu
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcomm a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [hsqA a ha, hsqB b hb, one_mul]
  · obtain ⟨f, hf, hfr⟩ := PumpRigid.exists_injective_prod hcomm hi
    have h1 : Nat.card (↥A × ↥B) = Nat.card ↥f.range :=
      Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    rw [Nat.card_prod] at h1
    rw [h1]
    exact Subgroup.card_le_of_le hfr

omit [Finite G] in
theorem three_cycle_conj {g z f : G} (h1 : g * f * g⁻¹ = z) (h2 : g * z * g⁻¹ = f) {m : ℕ}
    (hm : ¬ 2 ∣ m) : g ^ m * z * (g ^ m)⁻¹ = f := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  have hz : (g * g) * z = z * (g * g) := by
    calc (g * g) * z = g * (g * z * g⁻¹) * g := by group
      _ = g * f * g := by rw [h2]
      _ = (g * f * g⁻¹) * g * g := by group
      _ = z * (g * g) := by rw [h1]; group
  have hf : (g * g) * f = f * (g * g) := by
    calc (g * g) * f = g * (g * f * g⁻¹) * g := by group
      _ = g * z * g := by rw [h1]
      _ = (g * z * g⁻¹) * g * g := by group
      _ = f * (g * g) := by rw [h2]; group
  have hpf : ((g * g) ^ k) * f = f * ((g * g) ^ k) := (Commute.pow_left (show Commute (g * g) f from hf) k).eq
  have hpz : ((g * g) ^ k) * z = z * ((g * g) ^ k) := (Commute.pow_left (show Commute (g * g) z from hz) k).eq
  have hgm : g ^ (2 * k + 1) = (g * g) ^ k * g := by
    rw [pow_succ, pow_mul, sq]
  rw [hgm]
  calc (g * g) ^ k * g * z * ((g * g) ^ k * g)⁻¹ = (g * g) ^ k * (g * z * g⁻¹) * ((g * g) ^ k)⁻¹ := by group
    _ = (g * g) ^ k * f * ((g * g) ^ k)⁻¹ := by rw [h2]
    _ = f := by rw [hpf]; group

omit [Finite G] in
theorem exists_odd_pow_mem [Finite G] {V : Subgroup G} {g : G} (hVsyl : IsSylowOf 2 V ⊤)
    (hgN : g ∈ normalizer (V : Set G)) : ∃ m : ℕ, ¬ 2 ∣ m ∧ g ^ m ∈ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L : Subgroup G := V ⊔ zpowers g with hL
  have hVL : V ≤ L := le_sup_left
  have hLN : L ≤ normalizer (V : Set G) := sup_le Subgroup.le_normalizer ((zpowers_le).2 hgN)
  have hnormal : (V.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVL).2 hLN
  have hsyl : IsSylowOf 2 V L := hVsyl.of_le hVL le_top
  have hodd : ¬ 2 ∣ V.relIndex L := (isSylowOf_iff.1 hsyl).2.2
  have hgL : g ∈ L := Subgroup.mem_sup_right (mem_zpowers g)
  refine ⟨V.relIndex L, hodd, ?_⟩
  have hidx : V.relIndex L = Nat.card (↥L ⧸ V.subgroupOf L) := rfl
  have hpow : (QuotientGroup.mk ⟨g, hgL⟩ : ↥L ⧸ V.subgroupOf L) ^ Nat.card (↥L ⧸ V.subgroupOf L) = 1 :=
    pow_card_eq_one'
  rw [← hidx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hpow
  exact hpow

omit [Finite G] in
theorem elemAbelian_map_conj {U : Subgroup G} (h : IsElementaryAbelian 2 ↥U) (g : G) :
    IsElementaryAbelian 2 ↥(U.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hab, hsq⟩ := Back.forall_of_isElementaryAbelian h
  refine Back.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
  · obtain ⟨a, ha, rfl⟩ := mem_map_conj.1 hu
    obtain ⟨b, hb, rfl⟩ := mem_map_conj.1 hv
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hab a ha b hb]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  · obtain ⟨a, ha, rfl⟩ := mem_map_conj.1 hu
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hsq a ha]; group

theorem Env33.false_f_V_eq_W (E : Env33 x y K T V W f z) (hG : C3Hyp G)
    (h8 : 8 ≤ Nat.card ↥(secD K f V)) (hVW : V = W) {g : G} (hgN : g ∈ normalizer (V : Set G))
    (hgf : g * f * g⁻¹ = z) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hgn, hgn'⟩ := normalizer_conj_mem hgN
  have hVsyl : IsSylowOf 2 V ⊤ := hVW ▸ E.cfg.sylowW
  obtain ⟨m, hm, hgm⟩ := exists_odd_pow_mem hVsyl hgN
  have hZV := E.hZV h8
  have hzf_comm : z * f = f * z := (E.hfP z E.hzP).symm
  have hfZ : f ∈ zCenter V := ⟨E.cfg.f_mem_V, fun v hv => E.hVf v hv⟩
  have hzZ : z ∈ zCenter V := E.hzZ
  have hzf_ne : z ≠ f := fun h => E.hzD (h ▸ E.hfD)
  have hgz : g * z * g⁻¹ = z * f := by
    have hgzZ : g * z * g⁻¹ ∈ zpowers z ⊔ zpowers f := by
      rw [← hZV]; exact (zCenter_conj hgN).1 z hzZ
    rcases klein_cases E.hz2' E.hf2' hzf_comm hgzZ with h | h | h | h
    · exfalso
      apply E.hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply hzf_ne
      have h1 : g * f * g⁻¹ = g * z * g⁻¹ := by rw [hgf, h]
      have := (MulAut.conj g).injective (show (MulAut.conj g) f = (MulAut.conj g) z from h1)
      exact this.symm
    · exfalso
      have h1 := three_cycle_conj hgf h hm
      have h2 : g ^ m * z = z * g ^ m := hzZ.2 (g ^ m) hgm
      apply hzf_ne
      calc z = g ^ m * z * (g ^ m)⁻¹ := by rw [h2]; group
        _ = f := h1
    · exact h
  have hgg : g * g ∈ normalizer (V : Set G) := (normalizer (V : Set G)).mul_mem hgN hgN
  have hg2f : (g * g) * f * (g * g)⁻¹ = z * f := by
    calc (g * g) * f * (g * g)⁻¹ = g * (g * f * g⁻¹) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hgf]
      _ = z * f := hgz
  have hgf1 : g * f * g⁻¹ ≠ f := by rw [hgf]; exact hzf_ne
  have hgg_f : (g * g) * f * (g * g)⁻¹ ≠ f := by
    rw [hg2f]
    intro h
    apply E.hz1
    calc z = z * f * f⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨hD'V, hD'n, hDD', hcommD⟩ := E.conj_data hZV hgN hgf1
  obtain ⟨hD''V, hD''n, hDD'', hcommD''⟩ := E.conj_data hZV hgg hgg_f
  set D := secD K f V with hD
  set D' := D.map (MulAut.conj g).toMonoidHom with hD'
  set D'' := D.map (MulAut.conj (g * g)).toMonoidHom with hD''
  have hcomm' : ∀ e ∈ D', ∀ e' ∈ D'', e * e' = e' * e := by
    intro e he e' he'
    obtain ⟨d, hd, rfl⟩ := mem_map_conj.1 he
    obtain ⟨d'', hd'', rfl⟩ := mem_map_conj.1 he'
    have h := hcommD d hd (g * d'' * g⁻¹) (mem_map_conj.2 ⟨d'', hd'', rfl⟩)
    calc g * d * g⁻¹ * (g * g * d'' * (g * g)⁻¹) = g * (d * (g * d'' * g⁻¹)) * g⁻¹ := by group
      _ = g * ((g * d'' * g⁻¹) * d) * g⁻¹ := by rw [h]
      _ = g * g * d'' * (g * g)⁻¹ * (g * d * g⁻¹) := by group
  have hxf : x * f = f * x := E.cfg.hxf
  have hxne : zpowers x ⊓ zpowers f = ⊥ := by
    refine eq_bot_iff.2 (fun w hw => ?_)
    obtain ⟨h1, h2⟩ := hw
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers E.hx2 h1 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exfalso
      rcases Thm1P310.eq_one_or_eq_of_mem_zpowers E.hf2' h2 with h' | h'
      · exact E.hx1 (h.symm.trans h')
      · exact E.hxf_ne (h.symm.trans h')
  obtain ⟨hE₁ea, hE₁card⟩ := elemAbelian_sup_of_commute (elemAbelian_zpowers E.hx2)
    (elemAbelian_zpowers E.hf2')
    (fun a ha b hb => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow hxf i j).eq) hxne
  set E₁ : Subgroup G := zpowers x ⊔ zpowers f with hE₁
  have hxcard : Nat.card ↥(zpowers x) = 2 := by rw [Nat.card_zpowers, E.cfg.hx2]
  have hfcard : Nat.card ↥(zpowers f) = 2 := by rw [Nat.card_zpowers, E.cfg.hf2]
  rw [hxcard, hfcard] at hE₁card
  have hE₁D : E₁ ≤ D := sup_le ((zpowers_le).2 E.hxD) ((zpowers_le).2 E.hfD)
  set E₂ : Subgroup G := E₁.map (MulAut.conj g).toMonoidHom with hE₂
  have hE₂ea : IsElementaryAbelian 2 ↥E₂ := elemAbelian_map_conj hE₁ea g
  have hE₂card : Nat.card ↥E₂ = Nat.card ↥E₁ :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hE₂D' : E₂ ≤ D' := Subgroup.map_mono hE₁D
  have hE₁₂bot : E₁ ⊓ E₂ = ⊥ := by
    refine eq_bot_iff.2 (fun w hw => ?_)
    have : w ∈ D ⊓ D' := ⟨hE₁D hw.1, hE₂D' hw.2⟩
    rw [hDD', Subgroup.mem_bot] at this
    rw [this]; exact Subgroup.one_mem _
  have hcomm12 : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb =>
    hcommD a (hE₁D ha) b (hE₂D' hb)
  obtain ⟨hE₁₂ea, hE₁₂card⟩ := elemAbelian_sup_of_commute hE₁ea hE₂ea hcomm12 hE₁₂bot
  have h16 : 16 ≤ Nat.card ↥(E₁ ⊔ E₂) := by
    rw [hE₂card] at hE₁₂card
    nlinarith
  set x₃ : G := (g * g) * x * (g * g)⁻¹ with hx₃
  have hx₃D'' : x₃ ∈ D'' := mem_map_conj.2 ⟨x, E.hxD, rfl⟩
  have hx₃2 : x₃ * x₃ = 1 := by
    calc x₃ * x₃ = (g * g) * (x * x) * (g * g)⁻¹ := by rw [hx₃]; group
      _ = 1 := by rw [E.hx2]; group
  have hx₃1 : x₃ ≠ 1 := by
    intro h
    apply E.hx1
    calc x = (g * g)⁻¹ * x₃ * (g * g) := by rw [hx₃]; group
      _ = 1 := by rw [h]; group
  have hx₃c : ∀ a ∈ E₁ ⊔ E₂, a * x₃ = x₃ * a := by
    intro a ha
    obtain ⟨u, hu, v, hv, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hcomm12 ha
    have h1 : u * x₃ = x₃ * u := hcommD'' u (hE₁D hu) x₃ hx₃D''
    have h2 : v * x₃ = x₃ * v := hcomm' v (hE₂D' hv) x₃ hx₃D''
    calc u * v * x₃ = u * (v * x₃) := by group
      _ = u * (x₃ * v) := by rw [h2]
      _ = (u * x₃) * v := by group
      _ = (x₃ * u) * v := by rw [h1]
      _ = x₃ * (u * v) := by group
  have hx₃nm : x₃ ∉ E₁ ⊔ E₂ := by
    intro hmem
    have hmemD : x₃ ∈ D ⊔ D' := (sup_le_sup hE₁D hE₂D') hmem
    obtain ⟨a, ha, b, hb, hab⟩ := Thm1P310.exists_mul_of_mem_sup hcommD hmemD
    have haZ : a ∈ zCenter D := by
      refine ⟨ha, fun d hd => ?_⟩
      have h1 : x₃ * d = d * x₃ := (hcommD'' d hd x₃ hx₃D'').symm
      have h2 : d * b = b * d := hcommD d hd b hb
      rw [hab] at h1
      have h3 : d * a * b = a * d * b := by
        calc d * a * b = d * (a * b) := by group
          _ = a * b * d := h1.symm
          _ = a * (b * d) := by group
          _ = a * (d * b) := by rw [h2]
          _ = a * d * b := by group
      exact mul_right_cancel h3
    rw [E.hZD h8] at haZ
    have hbZ : ∀ e ∈ D', e * b = b * e := by
      intro e he
      have h1 : e * x₃ = x₃ * e := hcomm' e he x₃ hx₃D''
      have h2 : a * e = e * a := hcommD a ha e he
      rw [hab] at h1
      have h3 : a * (e * b) = a * (b * e) := by
        calc a * (e * b) = (a * e) * b := by group
          _ = (e * a) * b := by rw [h2]
          _ = e * (a * b) := by group
          _ = a * b * e := h1
          _ = a * (b * e) := by group
      exact mul_left_cancel h3
    obtain ⟨b', hb', hb'eq⟩ := mem_map_conj.1 hb
    have hb'Z : b' ∈ zCenter D := by
      refine ⟨hb', fun d hd => ?_⟩
      have h1 := hbZ (g * d * g⁻¹) (mem_map_conj.2 ⟨d, hd, rfl⟩)
      rw [← hb'eq] at h1
      calc d * b' = g⁻¹ * (g * d * g⁻¹ * (g * b' * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * b' * g⁻¹ * (g * d * g⁻¹)) * g := by rw [h1]
        _ = b' * d := by group
    rw [E.hZD h8] at hb'Z
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hb'Z
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 haZ
    have hbz : b = z ^ k := by
      rw [← hb'eq, ← hk]
      calc g * f ^ k * g⁻¹ = (g * f * g⁻¹) ^ k := conj_zpow.symm
        _ = z ^ k := by rw [hgf]
    have hx₃Z : x₃ ∈ zCenter V := by
      rw [hab, hbz, ← hj]
      exact (zCenter V).mul_mem ((zCenter V).zpow_mem hfZ j) ((zCenter V).zpow_mem hzZ k)
    have hxZ : x ∈ zCenter V := by
      have := (zCenter_conj hgg).2 x₃ hx₃Z
      have h' : (g * g)⁻¹ * x₃ * (g * g) = x := by rw [hx₃]; group
      rw [h'] at this
      exact this
    obtain ⟨d, hd, hdx⟩ := E.hx_not_cent h8
    exact hdx (hxZ.2 d (E.hDV hd))
  have hE₃bot : (E₁ ⊔ E₂) ⊓ zpowers x₃ = ⊥ := by
    refine eq_bot_iff.2 (fun w hw => ?_)
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers hx₃2 hw.2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd (h ▸ hw.1) hx₃nm
  obtain ⟨hEea, hEcard⟩ := elemAbelian_sup_of_commute hE₁₂ea (elemAbelian_zpowers hx₃2)
    (fun a ha b hb => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (show Commute a x₃ from hx₃c a ha) i).eq) hE₃bot
  have hx₃card : Nat.card ↥(zpowers x₃) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hx₃2) hx₃1]
  rw [hx₃card] at hEcard
  have hle := CFSG.Quasithin.BlueprintB2.card_le_pow_pRank (R := G) (p := 2) hEea
  rw [hG.pRank_eq_four] at hle
  omega

theorem Env33.layer_fz_ne_bot (hG : C3Hyp G) (E : Env33 x y K T V W f z)
    (hL2 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    pLayerOf 2 (K ⊓ centralizer ({f * z} : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ := exists_E₁ E.cfg.setup.sylowT
    (by rw [E.cfg.hu2.2.2.1.2, hG.pRank_eq_four])
  obtain ⟨f₁, z₁, -, -, -, -, -, -, -, hz₁, hz₁2, hz₁c, hz₁u, -, -, -, hlay⟩ :=
    core_lift_G E.cfg.hKx E.hKN E.cfg.setup.sylowT E.hcen E.hAut hE₁T hE₁ hE₁16 E.hQ2
  have hzC : z ∈ centralizer ({x} : Set G) := E.cfg.setup.sylowT.le E.hzP.1
  have hfzC : f * z ∈ centralizer ({x} : Set G) := Subgroup.mul_mem _ E.hfC hzC
  have hfz : f * z = z * f := (E.hfP z E.hzP)
  have hφz : Back.actHom E.hKN ⟨z, hzC⟩ ∈ innAut (kBar K) := by
    rw [Back.actHom_of_mem E.hKN E.hzP.2 hzC]
    exact ⟨_, rfl⟩
  have hφfz_eq : Back.actHom E.hKN ⟨f * z, hfzC⟩ =
      Back.actHom E.hKN ⟨f, E.hfC⟩ * Back.actHom E.hKN ⟨z, hzC⟩ := by
    have h1 := (Back.actHom E.hKN).map_mul ⟨f, E.hfC⟩ ⟨z, hzC⟩
    have e : (⟨f, E.hfC⟩ * ⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) = ⟨f * z, hfzC⟩ := rfl
    rw [e] at h1
    exact h1
  have hφfzinn : Back.actHom E.hKN ⟨f * z, hfzC⟩ ∉ innAut (kBar K) := by
    intro h
    apply E.hfout
    rw [hφfz_eq] at h
    have := (innAut (kBar K)).mul_mem h ((innAut (kBar K)).inv_mem hφz)
    simpa using this
  have hfz1 : f * z ≠ 1 := by
    intro h
    apply hφfzinn
    have : (⟨f * z, hfzC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext h
    rw [this, map_one]
    exact (innAut (kBar K)).one_mem
  have hfz2 : orderOf (f * z) = 2 :=
    orderOf_mul_eq_two_of_commute E.cfg.hf2 E.hz2 hfz hfz1
  have hfzT : f * z ∈ T := T.mul_mem E.cfg.mem.1 E.hzP.1
  have hfzCT : (⟨f * z, hfzC⟩ : ↥(centralizer ({x} : Set G))) ∈
      T.subgroupOf (centralizer ({x} : Set G)) := hfzT
  have hfz2' : orderOf (⟨f * z, hfzC⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hfz2
  have hfc' : ∀ p ∈ (T ⊓ K).subgroupOf (centralizer ({x} : Set G)),
      (⟨f * z, hfzC⟩ : ↥(centralizer ({x} : Set G))) * p = p * ⟨f * z, hfzC⟩ := by
    intro p hp
    have hp' : (p : G) ∈ T ⊓ K := hp
    apply Subtype.ext
    show f * z * (p : G) = (p : G) * (f * z)
    have h1 : f * (p : G) = (p : G) * f := E.hfP p hp'
    have h2 : (p : G) * z = z * (p : G) := E.cfg.z_mem.2.2 p hp'.1
    calc f * z * (p : G) = f * (z * (p : G)) := by group
      _ = f * ((p : G) * z) := by rw [h2]
      _ = (f * (p : G)) * z := by group
      _ = ((p : G) * f) * z := by rw [h1]
      _ = (p : G) * (f * z) := by group
  rcases hlay ⟨f * z, hfzC⟩ hfzCT hfz2' hfc' hφfzinn with hg | ⟨hA7, -⟩
  · exact layer_ne_bot_of_good E.hKN hfzC hfz2 hg
  · exact absurd hA7 hL2

theorem Env33.hfzC (E : Env33 x y K T V W f z) : f * z ∈ centralizer ({x} : Set G) :=
  Subgroup.mul_mem _ E.hfC (E.cfg.setup.sylowT.le E.hzP.1)

theorem Env33.hφfz_not_inn (E : Env33 x y K T V W f z) :
    Back.actHom E.hKN ⟨f * z, E.hfzC⟩ ∉ innAut (kBar K) := by
  have hzC : z ∈ centralizer ({x} : Set G) := E.cfg.setup.sylowT.le E.hzP.1
  have hφz : Back.actHom E.hKN ⟨z, hzC⟩ ∈ innAut (kBar K) := by
    rw [Back.actHom_of_mem E.hKN E.hzP.2 hzC]
    exact ⟨_, rfl⟩
  have hφfz_eq : Back.actHom E.hKN ⟨f * z, E.hfzC⟩ =
      Back.actHom E.hKN ⟨f, E.hfC⟩ * Back.actHom E.hKN ⟨z, hzC⟩ := by
    have h1 := (Back.actHom E.hKN).map_mul ⟨f, E.hfC⟩ ⟨z, hzC⟩
    have e : (⟨f, E.hfC⟩ * ⟨z, hzC⟩ : ↥(centralizer ({x} : Set G))) = ⟨f * z, E.hfzC⟩ := rfl
    rw [e] at h1
    exact h1
  intro h
  apply E.hfout
  rw [hφfz_eq] at h
  have := (innAut (kBar K)).mul_mem h ((innAut (kBar K)).inv_mem hφz)
  simpa using this

theorem Env33.fz_basic (E : Env33 x y K T V W f z) :
    f * z ∈ T ∧ orderOf (f * z) = 2 ∧ (∀ p ∈ T ⊓ K, f * z * p = p * (f * z)) ∧ f * z ≠ x := by
  refine ⟨T.mul_mem E.cfg.mem.1 E.hzP.1, ?_, ?_, ?_⟩
  · refine orderOf_mul_eq_two_of_commute E.cfg.hf2 E.hz2 (E.hfP z E.hzP) ?_
    intro h
    apply E.hφfz_not_inn
    have : (⟨f * z, E.hfzC⟩ : ↥(centralizer ({x} : Set G))) = 1 := Subtype.ext h
    rw [this, map_one]
    exact (innAut (kBar K)).one_mem
  · intro p hp
    have h1 : f * p = p * f := E.hfP p hp
    have h2 : p * z = z * p := E.cfg.z_mem.2.2 p hp.1
    calc f * z * p = f * (z * p) := by group
      _ = f * (p * z) := by rw [h2]
      _ = (f * p) * z := by group
      _ = (p * f) * z := by rw [h1]
      _ = p * (f * z) := by group
  · intro h
    apply E.hφfz_not_inn
    have : (⟨f * z, E.hfzC⟩ : ↥(centralizer ({x} : Set G))) = ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ :=
      Subtype.ext h
    rw [this, E.hxker]
    exact (innAut (kBar K)).one_mem

theorem Env33.card_secD_cases (E : Env33 x y K T V W f z) :
    Nat.card ↥(secD K f V) = 4 ∨ 8 ≤ Nat.card ↥(secD K f V) := by
  have h4 := E.cfg.four_le_card_secD E.hsup E.hJn
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (E.hV2.to_le E.hDV)
  rw [hn] at h4 ⊢
  by_cases hn3 : 3 ≤ n
  · right
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  · left
    interval_cases n <;> simp_all

end F

end CFSG.GH74.GLS.C3.Layer1.Thm1G33

