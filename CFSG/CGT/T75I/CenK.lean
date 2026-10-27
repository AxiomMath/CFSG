module

public import CFSG.CGT.T75I.CenFacts
public import CFSG.CGT.T75I.Cen2
public import CFSG.CGT.T75I.CenBasic
public import CFSG.CGT.T75I.CenCM
public import CFSG.CGT.T75I.CenX1
public import CFSG.CGT.T75I.DMax

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem exists_x₀ (hc : Sec6Ctx T T₁ 2 2) :
    ∃ x₀ : G, x₀ ∈ normIn T₁ T ∧ x₀ ≠ 1 ∧ x₀ ∈ normD T ∧ x₀ ∉ T := by
  have hS3 : Sec3 T T₁ := hc.sec3
  obtain ⟨x₀, hx₀L, hx₀1⟩ : ∃ x₀ ∈ normIn T₁ T, x₀ ≠ 1 := by
    obtain ⟨⟨d, hd⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hS3.cfg.ne₁
    exact ⟨d, hd, fun h => hne1 (Subtype.ext h)⟩
  obtain ⟨g, -, hgT₁⟩ := hS3.conj
  have hx₀T₁ : x₀ ∈ T₁ := normIn_le _ _ hx₀L
  have hx₀N : x₀ ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hx₀L).2
  refine ⟨x₀, hx₀L, hx₀1, mem_normD_of_mem_conjSubgroup (k := g)
    (by rw [← hgT₁]; exact hx₀T₁) hx₀1 hx₀N, ?_⟩
  intro hT'
  have : x₀ ∈ T ⊓ T₁ := ⟨hT', hx₀T₁⟩
  rw [hS3.cfg.inf, Subgroup.mem_bot] at this
  exact hx₀1 this

theorem mem_centralizer_of_mem {t : G} (hTab : IsElemAbelian 2 T) (ht : t ∈ T) :
    t ∈ Subgroup.centralizer (T : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun _ hh => elemAbelian_mul_comm hTab hh ht

theorem exists_fixed_in_X₁ [Finite G] [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]
    (hS : Sec3 T T₁) {q : ℕ}
    (hpair : IsL2Pair (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) q)
    {u : G} (huT : u ∈ Subgroup.centralizer (T : Set G)) (huT₁ : conjSubgroup u T₁ = T₁) :
    ∃ a ∈ cfgM T T₁, ∀ x ∈ T ⊔ T₁, x * (u * a) * x⁻¹ = u * a := by
  classical
  have hcomm1 := comm_mem_cfgM_of_centralizer hS hpair huT huT₁
  have hcomm2 := conj_eq_of_centralizer hS hpair huT huT₁
  have hMab := hS.cfg.isElemAbelian_cfgM
  have hu : ∀ x ∈ T ⊔ T₁, u⁻¹ * (x * u * x⁻¹) ∈ cfgM T T₁ := by
    intro x hx
    have h1' := hcomm1 x⁻¹ ((T ⊔ T₁).inv_mem hx)
    have hm : x * u * x⁻¹ * u⁻¹ ∈ cfgM T T₁ := by simpa [mul_assoc] using h1'
    obtain ⟨m, hmdef⟩ : ∃ m : G, m = x * u * x⁻¹ * u⁻¹ := ⟨_, rfl⟩
    have hmM : m ∈ cfgM T T₁ := hmdef ▸ hm
    have hxu : x * u * x⁻¹ = m * u := by rw [hmdef]; group
    have hmu : m * u = u * m := by
      have := hcomm2 m hmM
      calc m * u = (u * m * u⁻¹) * u := by rw [this]
        _ = u * m := by group
    have : u⁻¹ * (x * u * x⁻¹) = m := by rw [hxu, hmu]; group
    rw [this]
    exact hmM
  refine exists_fixed_of_odd_index (X := T ⊔ T₁) (A := cfgM T T₁)
    (fun a ha => elemAbelian_mul_self hMab ha) (fun a ha b hb => elemAbelian_mul_comm hMab ha hb)
    (fun x hx a ha => hS.cfg.conj_mem_cfgM hx ha) hu
    (S := ((T.subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))).comap
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) ?_ ?_
  · intro s' hs'
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hs')
    have h2 : (t : G)⁻¹ * (s' : G) ∈ cfgM T T₁ :=
      Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hts)
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have htu : (t : G) * u = u * t := Subgroup.mem_centralizer_iff.1 huT t htT
    clear hts ht
    obtain ⟨tg, htg⟩ : ∃ tg : G, tg = (t : G) := ⟨_, rfl⟩
    obtain ⟨sg, hsg⟩ : ∃ sg : G, sg = (s' : G) := ⟨_, rfl⟩
    rw [← htg] at h2 htT htu
    rw [← hsg] at h2 ⊢
    obtain ⟨m, hm⟩ : ∃ m : G, m = tg⁻¹ * sg := ⟨_, rfl⟩
    have hmM : m ∈ cfgM T T₁ := hm ▸ h2
    have hs'eq : sg = tg * m := by rw [hm]; group
    have hmu : m * u = u * m := by
      have := hcomm2 m hmM
      calc m * u = (u * m * u⁻¹) * u := by rw [this]
        _ = u * m := by group
    calc sg * u * sg⁻¹ = tg * (m * u) * m⁻¹ * tg⁻¹ := by rw [hs'eq]; group
      _ = tg * (u * m) * m⁻¹ * tg⁻¹ := by rw [hmu]
      _ = tg * u * tg⁻¹ := by group
      _ = u := by rw [htu]; group
  · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact odd_index_of_pair hpair

theorem exists_decomp (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ 2 2)
    [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hperf : commutator (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) = ⊤)
    {c : G} (hcC : c ∈ Subgroup.centralizer (T : Set G)) :
    ∃ k t : G, k ∈ Subgroup.centralizer (T : Set G) ∧ k ∈ Subgroup.centralizer (T₁ : Set G) ∧
      t ∈ T ∧ c = k * t := by
  classical
  have : Finite G := hc.finite
  have hS3 : Sec3 T T₁ := hc.sec3
  have hTab := hc.hy.pair.wc.1
  obtain ⟨hN, hiso⟩ := ctx_exists_iso_two hc
  have hpair := hS3.isL2Pair_quotient (f := 2) (by norm_num) hiso
  obtain ⟨x₀, hx₀L, hx₀1, hx₀normD, hx₀nT⟩ := exists_x₀ hc
  have hx₀T₁ : x₀ ∈ T₁ := normIn_le _ _ hx₀L
  have hx₀H : x₀ ∈ hSub T (normIn T₁ T) := le_hSub hx₀L
  have hcomm : ⁅x₀⁻¹, c⁆ ∈ T :=
    comm_mem_of_centralizer h1 hc hperf hcC ((hSub T (normIn T₁ T)).inv_mem hx₀H)
  have hyD : c * x₀ * c⁻¹ ∈ classD T := by
    have := classD_conj hx₀normD.1 c⁻¹
    simpa using this
  have hyt : x₀⁻¹ * (c * x₀ * c⁻¹) ∈ T := by
    simpa [commutatorElement_def, mul_assoc] using hcomm
  obtain ⟨s, hsT, hs⟩ := hc.eq_conj_of_mem_coset h62 h63 hx₀normD hx₀nT hyD hyt (by group)
  have hsC : s ∈ Subgroup.centralizer (T : Set G) := mem_centralizer_of_mem hTab hsT
  have huC : s * c ∈ Subgroup.centralizer (T : Set G) := Subgroup.mul_mem _ hsC hcC
  have hux₀ : (s * c) * x₀ * (s * c)⁻¹ = x₀ := by
    calc (s * c) * x₀ * (s * c)⁻¹ = s * (c * x₀ * c⁻¹) * s⁻¹ := by group
      _ = s * (s⁻¹ * x₀ * s) * s⁻¹ := by rw [hs]
      _ = x₀ := by group
  have huN₁ : s * c ∈ Subgroup.normalizer (T₁ : Set G) :=
    hS3.cfg.wc₁.centralizer_le_normalizer hx₀T₁ hx₀1 (Subgroup.mem_centralizer_singleton_iff.2 (by
      calc s * c * x₀ = ((s * c) * x₀ * (s * c)⁻¹) * (s * c) := by group
        _ = x₀ * (s * c) := by rw [hux₀]))
  have huT₁ : conjSubgroup (s * c) T₁ = T₁ := mem_normalizer_iff_conjSubgroup_eq.1 huN₁
  obtain ⟨a, haM, ha⟩ := exists_fixed_in_X₁ hS3 hpair huC huT₁
  have hkT : s * c * a ∈ Subgroup.centralizer (T : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
    have := ha t (Subgroup.mem_sup_left ht)
    calc t * (s * c * a) = (t * (s * c * a) * t⁻¹) * t := by group
      _ = (s * c * a) * t := by rw [this]
  have hkT₁ : s * c * a ∈ Subgroup.centralizer (T₁ : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
    have := ha t (Subgroup.mem_sup_right ht)
    calc t * (s * c * a) = (t * (s * c * a) * t⁻¹) * t := by group
      _ = (s * c * a) * t := by rw [this]
  have haC : a ∈ Subgroup.centralizer (T : Set G) := by
    have := Subgroup.mul_mem _ ((Subgroup.centralizer (T : Set G)).inv_mem huC) hkT
    simpa [mul_assoc] using this
  obtain ⟨l, hl, x, hx, hlx⟩ := hS3.cfg.mem_cfgM_iff.1 haM
  have hlT : l ∈ T := normIn_le _ _ hl
  have hxT₁ : x ∈ T₁ := normIn_le _ _ hx
  have hx1 : x = 1 := by
    refine ctx_eq_one_of_centralizes_T hc hxT₁ fun t ht => ?_
    have hat := Subgroup.mem_centralizer_iff.1 haC t ht
    have hxeq : x = l⁻¹ * a := by rw [hlx]; group
    have hlt : l⁻¹ * t = t * l⁻¹ := elemAbelian_mul_comm hTab (T.inv_mem hlT) ht
    calc x * t = l⁻¹ * (a * t) := by rw [hxeq]; group
      _ = l⁻¹ * (t * a) := by rw [hat]
      _ = t * (l⁻¹ * a) := by rw [← mul_assoc, hlt]; group
      _ = t * x := by rw [hxeq]
  have haT : a ∈ T := by
    have : a = l := by rw [hlx, hx1, mul_one]
    rw [this]
    exact hlT
  refine ⟨s * c * a, s⁻¹ * a⁻¹, hkT, hkT₁, T.mul_mem (T.inv_mem hsT) (T.inv_mem haT), ?_⟩
  have hcs : c * s⁻¹ = s⁻¹ * c :=
    (Subgroup.mem_centralizer_iff.1 hcC s⁻¹ (T.inv_mem hsT)).symm
  have has : a * s⁻¹ = s⁻¹ * a := elemAbelian_mul_comm hTab haT (T.inv_mem hsT)
  have hfinal : (s * c * a) * (s⁻¹ * a⁻¹) = c := by
    calc (s * c * a) * (s⁻¹ * a⁻¹) = s * c * (a * s⁻¹) * a⁻¹ := by group
      _ = s * c * (s⁻¹ * a) * a⁻¹ := by rw [has]
      _ = s * (c * s⁻¹) * (a * a⁻¹) := by group
      _ = s * (s⁻¹ * c) * (a * a⁻¹) := by rw [hcs]
      _ = c := by group
  exact hfinal.symm

theorem odd_index_stabilizer (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ 2 2)
    [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hhat : IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
      IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))))
    {k : G} (hkT : k ∈ Subgroup.centralizer (T : Set G))
    (hkT₁ : k ∈ Subgroup.centralizer (T₁ : Set G)) :
    Odd ((Subgroup.centralizer ({k} : Set G)).subgroupOf (hSub T (normIn T₁ T))).index := by
  classical
  have : Finite G := hc.finite
  have hperf := perfect_of_hat hhat
  have hS3 : Sec3 T T₁ := hc.sec3
  have hTab := hc.hy.pair.wc.1
  set H := hSub T (normIn T₁ T) with hH
  obtain ⟨x₀, hx₀L, hx₀1, hx₀normD, hx₀nT⟩ := exists_x₀ hc
  have hx₀T₁ : x₀ ∈ T₁ := normIn_le _ _ hx₀L
  have hx₀H : x₀ ∈ H := le_hSub hx₀L
  let π : ↥H →* ↥H ⧸ T.subgroupOf H := QuotientGroup.mk' (T.subgroupOf H)
  let x₀' : ↥H := ⟨x₀, hx₀H⟩
  have hπ1 : ∀ z : ↥H, π z = 1 → (z : G) ∈ T := fun z hz =>
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff z).1 hz)
  have hx₀2 : x₀ * x₀ = 1 := mul_self_eq_one_of_mem_classD hTab hx₀normD.1
  have hπx1 : π x₀' ≠ 1 := fun h => hx₀nT (hπ1 x₀' h)
  have hπx2 : π x₀' * π x₀' = 1 := by
    rw [← map_mul]
    have : x₀' * x₀' = 1 := Subtype.ext hx₀2
    rw [this, map_one]
  have hodd := odd_index_centralizer_of_conj_involutions (exists_conj_involutions_of_hat hhat)
    hπx1 hπx2
  have hĈ : Odd ((Subgroup.centralizer ({π x₀'} : Set (↥H ⧸ T.subgroupOf H))).comap π).index := by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hodd
  refine Odd.of_dvd_nat hĈ (Subgroup.index_dvd_of_le ?_)
  intro h hh
  have hcomm : π h * π x₀' = π x₀' * π h :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 hh)
  have hconj : π x₀' = π (h * x₀' * h⁻¹) := by
    rw [map_mul, map_mul, map_inv, hcomm]
    group
  have key : x₀⁻¹ * ((h : G) * x₀ * (h : G)⁻¹) ∈ T := by
    have := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hconj)
    simpa using this
  have hyD : (h : G) * x₀ * (h : G)⁻¹ ∈ classD T := by
    have := classD_conj hx₀normD.1 (h : G)⁻¹
    simpa using this
  obtain ⟨s, hsT, hs⟩ := hc.eq_conj_of_mem_coset h62 h63 hx₀normD hx₀nT hyD key (by group)
  have hgx₀ : (s * (h : G)) * x₀ * (s * (h : G))⁻¹ = x₀ := by
    calc (s * (h : G)) * x₀ * (s * (h : G))⁻¹ = s * ((h : G) * x₀ * (h : G)⁻¹) * s⁻¹ := by group
      _ = s * (s⁻¹ * x₀ * s) * s⁻¹ := by rw [hs]
      _ = x₀ := by group
  have hgH : s * (h : G) ∈ H := H.mul_mem (left_le_hSub hsT) h.2
  have hgNT : s * (h : G) ∈ Subgroup.normalizer (T : Set G) := hSub_le_normalizer' hgH
  have hgN₁ : s * (h : G) ∈ Subgroup.normalizer (T₁ : Set G) :=
    hS3.cfg.wc₁.centralizer_le_normalizer hx₀T₁ hx₀1 (Subgroup.mem_centralizer_singleton_iff.2 (by
      calc s * (h : G) * x₀ = ((s * (h : G)) * x₀ * (s * (h : G))⁻¹) * (s * (h : G)) := by group
        _ = x₀ * (s * (h : G)) := by rw [hgx₀]))
  have hk'C : (s * (h : G)) * k * (s * (h : G))⁻¹ ∈ Subgroup.centralizer (T : Set G) :=
    conj_mem_centralizer hgNT hkT
  have hk'C₁ : (s * (h : G)) * k * (s * (h : G))⁻¹ ∈ Subgroup.centralizer (T₁ : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have hy' : (s * (h : G))⁻¹ * y * (s * (h : G)) ∈ T₁ := by
      have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T₁ : Set G)).inv_mem hgN₁) hy
      simpa using this
    have hk := Subgroup.mem_centralizer_iff.1 hkT₁ _ hy'
    calc y * ((s * (h : G)) * k * (s * (h : G))⁻¹)
        = (s * (h : G)) * (((s * (h : G))⁻¹ * y * (s * (h : G))) * k) * (s * (h : G))⁻¹ := by
          group
      _ = (s * (h : G)) * (k * ((s * (h : G))⁻¹ * y * (s * (h : G)))) * (s * (h : G))⁻¹ := by
          rw [hk]
      _ = ((s * (h : G)) * k * (s * (h : G))⁻¹) * y := by group
  have ht₀T : (s * (h : G)) * k * (s * (h : G))⁻¹ * k⁻¹ ∈ T := by
    have := comm_mem_of_centralizer h1 hc hperf hkT hgH
    simpa [commutatorElement_def] using this
  have ht₀C₁ : (s * (h : G)) * k * (s * (h : G))⁻¹ * k⁻¹ ∈ Subgroup.centralizer (T₁ : Set G) :=
    Subgroup.mul_mem _ hk'C₁ ((Subgroup.centralizer (T₁ : Set G)).inv_mem hkT₁)
  have ht₀1 : (s * (h : G)) * k * (s * (h : G))⁻¹ * k⁻¹ = 1 :=
    ctx_eq_one_of_centralizes_T₁ hc ht₀T fun y hy => (Subgroup.mem_centralizer_iff.1 ht₀C₁ y hy).symm
  have hgk : (s * (h : G)) * k * (s * (h : G))⁻¹ = k := mul_inv_eq_one.1 ht₀1
  have hsk : s * k = k * s := Subgroup.mem_centralizer_iff.1 hkT s hsT
  have hhk : (h : G) * k * (h : G)⁻¹ = k := by
    have e : (h : G) * k * (h : G)⁻¹ = s⁻¹ * ((s * (h : G)) * k * (s * (h : G))⁻¹) * s := by group
    rw [e, hgk]
    calc s⁻¹ * k * s = s⁻¹ * (k * s) := by group
      _ = s⁻¹ * (s * k) := by rw [hsk]
      _ = k := by group
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
  calc (h : G) * k = ((h : G) * k * (h : G)⁻¹) * (h : G) := by group
    _ = k * (h : G) := by rw [hhk]

theorem exists_fixed_point (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ 2 2)
    [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hhat : IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
      IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))))
    {k : G} (hkT : k ∈ Subgroup.centralizer (T : Set G))
    (hkT₁ : k ∈ Subgroup.centralizer (T₁ : Set G)) :
    ∃ t ∈ T, ∀ h ∈ hSub T (normIn T₁ T), h * (k * t) * h⁻¹ = k * t := by
  classical
  have : Finite G := hc.finite
  have hperf := perfect_of_hat hhat
  have hTab := hc.hy.pair.wc.1
  have hu : ∀ x ∈ hSub T (normIn T₁ T), k⁻¹ * (x * k * x⁻¹) ∈ T := by
    intro x hx
    have hcm : x * k * x⁻¹ * k⁻¹ ∈ T := by
      have := comm_mem_of_centralizer h1 hc hperf hkT hx
      simpa [commutatorElement_def] using this
    have hkt := Subgroup.mem_centralizer_iff.1 hkT _ hcm
    have : k⁻¹ * (x * k * x⁻¹) = x * k * x⁻¹ * k⁻¹ := by
      calc k⁻¹ * (x * k * x⁻¹) = k⁻¹ * ((x * k * x⁻¹ * k⁻¹) * k) := by group
        _ = k⁻¹ * (k * (x * k * x⁻¹ * k⁻¹)) := by rw [hkt]
        _ = x * k * x⁻¹ * k⁻¹ := by group
    rw [this]
    exact hcm
  have hS : ∀ s ∈ (Subgroup.centralizer ({k} : Set G)).subgroupOf (hSub T (normIn T₁ T)),
      (s : G) * k * (s : G)⁻¹ = k := by
    intro s hs
    have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hs)
    calc (s : G) * k * (s : G)⁻¹ = (k * (s : G)) * (s : G)⁻¹ := by rw [this]
      _ = k := by group
  obtain ⟨t, ht, hfix⟩ := exists_fixed_of_odd_index (X := hSub T (normIn T₁ T)) (A := T)
    (fun a ha => elemAbelian_mul_self hTab ha) (fun a ha b hb => elemAbelian_mul_comm hTab ha hb)
    (fun x hx a ha => conj_mem_of_mem_normalizer (hSub_le_normalizer' hx) ha) hu hS
    (odd_index_stabilizer h1 h62 h63 hc hhat hkT hkT₁)
  exact ⟨t, ht, hfix⟩

theorem eq_one_of_fixed (h57 : Step57) (hc : Sec6Ctx T T₁ 2 2) {k t : G} (hkT₁ : k ∈ Subgroup.centralizer (T₁ : Set G)) (htT : t ∈ T)
    (hfix : ∀ h ∈ hSub T (normIn T₁ T), h * (k * t) * h⁻¹ = k * t)
    (hkX : ∀ x ∈ T ⊔ T₁, x * k = k * x) : t = 1 := by
  classical
  have : Finite G := hc.finite
  have hS3 : Sec3 T T₁ := hc.sec3
  obtain ⟨hN, hiso⟩ := ctx_exists_iso_two hc
  obtain ⟨w, hwX, hwN, hw1, hwfree⟩ := ctx_exists_odd_element hc hiso
  obtain ⟨x₀, hx₀L, hx₀1, hx₀normD, hx₀nT⟩ := exists_x₀ hc
  have hx₀T₁ : x₀ ∈ T₁ := normIn_le _ _ hx₀L
  have hx₀H : x₀ ∈ hSub T (normIn T₁ T) := le_hSub hx₀L
  have hktN₁ : k * t ∈ Subgroup.normalizer (T₁ : Set G) :=
    hS3.cfg.wc₁.centralizer_le_normalizer hx₀T₁ hx₀1 (Subgroup.mem_centralizer_singleton_iff.2 (by
      have := hfix x₀ hx₀H
      calc k * t * x₀ = (x₀ * (k * t) * x₀⁻¹) * x₀ := by rw [this]
        _ = x₀ * (k * t) := by group))
  have hkN₁ : k ∈ Subgroup.normalizer (T₁ : Set G) :=
    Subgroup.centralizer_le_normalizer (T₁ : Set G) hkT₁
  have htN₁ : t ∈ Subgroup.normalizer (T₁ : Set G) := by
    have := (Subgroup.normalizer (T₁ : Set G)).mul_mem
      ((Subgroup.normalizer (T₁ : Set G)).inv_mem hkN₁) hktN₁
    simpa using this
  have htM : t ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_left T T₁ (mem_normIn.2 ⟨htT, htN₁⟩)
  have hktH : k * t ∈ Subgroup.centralizer (↑(hSub T (normIn T₁ T)) : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    have := hfix h hh
    calc h * (k * t) = (h * (k * t) * h⁻¹) * h := by group
      _ = (k * t) * h := by rw [this]
  have hwH : w * (k * t) * w⁻¹ ∈ Subgroup.centralizer (↑(hSub T (normIn T₁ T)) : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    have hh' : w⁻¹ * h * w ∈ hSub T (normIn T₁ T) := by
      have := conj_mem_hSub ((Subgroup.normalizer (T : Set G)).inv_mem hwN) hh
      simpa using this
    have := Subgroup.mem_centralizer_iff.1 hktH _ hh'
    calc h * (w * (k * t) * w⁻¹) = w * ((w⁻¹ * h * w) * (k * t)) * w⁻¹ := by group
      _ = w * ((k * t) * (w⁻¹ * h * w)) * w⁻¹ := by rw [this]
      _ = (w * (k * t) * w⁻¹) * h := by group
  have hwk : w * k * w⁻¹ = k := by
    have := hkX w hwX
    calc w * k * w⁻¹ = (k * w) * w⁻¹ := by rw [this]
      _ = k := by group
  have htw : w * t * w⁻¹ ∈ T := conj_mem_of_mem_normalizer hwN htT
  have hz : t⁻¹ * (w * t * w⁻¹) ∈ Subgroup.centralizer (↑(hSub T (normIn T₁ T)) : Set G) := by
    have := Subgroup.mul_mem _ ((Subgroup.centralizer (↑(hSub T (normIn T₁ T)) : Set G)).inv_mem
      hktH) hwH
    have e : (k * t)⁻¹ * (w * (k * t) * w⁻¹) = t⁻¹ * (w * t * w⁻¹) := by
      calc (k * t)⁻¹ * (w * (k * t) * w⁻¹)
          = t⁻¹ * k⁻¹ * ((w * k * w⁻¹) * (w * t * w⁻¹)) := by group
        _ = t⁻¹ * (w * t * w⁻¹) := by rw [hwk]; group
    rwa [e] at this
  have hz1 : t⁻¹ * (w * t * w⁻¹) = 1 :=
    ctx_eq_one_of_centralizes_hSub h57 hc (T.mul_mem (T.inv_mem htT) htw) fun x hx =>
      Subgroup.mem_centralizer_iff.1 hz x hx
  have hwt : w * t * w⁻¹ = t := (inv_mul_eq_one.1 hz1).symm
  exact hwfree t htM hwt

theorem centralizer_eq_of_ctx (h1 : Sec4NoA) (h57 : Step57) (h62 : Sec62) (h63 : Sec63)
    (hBen : AschbacherDisconnectedInput) (hc : Sec6Ctx T T₁ 2 2)
    [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hhat : IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
      IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)))) :
    Subgroup.centralizer (T : Set G) = T := by
  classical
  have : Finite G := hc.finite
  have : IsSimpleGroup G := hc.hy.simple
  have hTab := hc.hy.pair.wc.1
  refine le_antisymm (fun c hcC => ?_) (fun t ht => mem_centralizer_of_mem hTab ht)
  obtain ⟨k, t, hkT, hkT₁, htT, rfl⟩ :=
    exists_decomp h1 h62 h63 hc (perfect_of_hat hhat) hcC
  obtain ⟨t', ht', hfix⟩ := exists_fixed_point h1 h62 h63 hc hhat hkT hkT₁
  have hkX : ∀ x ∈ T ⊔ T₁, x * k = k * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1
      ((sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hkT t ht))
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hkT₁ y hy)) :
        T ⊔ T₁ ≤ Subgroup.centralizer ({k} : Set G)) hx)
  have ht'1 : t' = 1 := eq_one_of_fixed h57 hc hkT₁ ht' hfix hkX
  subst ht'1
  have hkH : ∀ h ∈ hSub T (normIn T₁ T), h * k = k * h := by
    intro h hh
    have := hfix h hh
    simp only [mul_one] at this
    calc h * k = (h * k * h⁻¹) * h := by group
      _ = k * h := by rw [this]
  have hcent : k ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro w
    have hw : w ∈ hSub T (normIn T₁ T) ⊔ T₁ := by
      rw [hSub_sup_eq_top h1 h57 h62 h63 hBen hc hhat]
      trivial
    have hle : hSub T (normIn T₁ T) ⊔ T₁ ≤ Subgroup.centralizer ({k} : Set G) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hkH x hx))
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hkT₁ y hy))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hw)
  have := center_eq_bot_of_simple_nonabelian G hc.hy.nonab
  rw [this, Subgroup.mem_bot] at hcent
  rw [hcent, one_mul]
  exact htT

end CFSG.CGT.T75I
