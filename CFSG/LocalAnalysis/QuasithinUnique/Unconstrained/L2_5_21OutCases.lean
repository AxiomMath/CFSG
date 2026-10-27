module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21OutAct

public section

open scoped commutatorElement

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Ctx

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G} {R : Subgroup ↥(autOn N.S N.K)}

structure OutCtx (N : Notation25 hs) (t zK : G) (R : Subgroup ↥(autOn N.S N.K)) : Prop where
  lv : Lv2520 N t zK
  par : CaseCParams N t zK R
  fam : OutFamily N.K N.H
  typ : IsL2pType ↥N.K
  ne : CFSG.conjugate N.K N.x ≠ N.K
  comm : ∀ k ∈ N.K, ∀ k' ∈ CFSG.conjugate N.K N.x, k * k' = k' * k

theorem OutCtx.zK_mem (c : OutCtx N t zK R) : zK ∈ N.K := c.lv.hK0 ▸ c.lv.facts2511.zK_mem

theorem OutCtx.t_mem_Kx (c : OutCtx N t zK R) : t ∈ CFSG.conjugate N.K N.x :=
  c.lv.t_mem_Kx c.par

theorem OutCtx.xinv_zK_x (c : OutCtx N t zK R) : N.x⁻¹ * zK * N.x = t := by
  have hf := c.lv.facts2511
  have hx2 : N.x * N.x ∈ N.S := by
    have := N.x_sq
    rwa [pow_two] at this
  have hc : (N.x * N.x) * t = t * (N.x * N.x) :=
    Subgroup.mem_centralizer_iff.mp hf.t_mem_center.2 _ hx2
  calc N.x⁻¹ * zK * N.x = N.x⁻¹ * (N.x⁻¹ * t * N.x) * N.x := by rw [c.par.htx]
    _ = (N.x * N.x)⁻¹ * t * (N.x * N.x) := by group
    _ = (N.x * N.x)⁻¹ * (t * (N.x * N.x)) := by group
    _ = (N.x * N.x)⁻¹ * ((N.x * N.x) * t) := by rw [hc]
    _ = t := by group

theorem OutCtx.centerless_Kx (c : OutCtx N t zK R) {z : G} (hz : z ∈ CFSG.conjugate N.K N.x)
    (hc : ∀ u ∈ CFSG.conjugate N.K N.x, z * u = u * z) : z = 1 := by
  have hz' : N.x * z * N.x⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hz
  have h1 : N.x * z * N.x⁻¹ = 1 := by
    refine c.lv.centerless_K _ hz' fun y hy => ?_
    have hu : N.x⁻¹ * y * N.x ∈ CFSG.conjugate N.K N.x := by
      rw [BenderBranch.mem_conjugate_iff]
      have : N.x * (N.x⁻¹ * y * N.x) * N.x⁻¹ = y := by group
      rw [this]; exact hy
    have h2 := hc _ hu
    calc N.x * z * N.x⁻¹ * y = N.x * (z * (N.x⁻¹ * y * N.x)) * N.x⁻¹ := by group
      _ = N.x * ((N.x⁻¹ * y * N.x) * z) * N.x⁻¹ := by rw [h2]
      _ = y * (N.x * z * N.x⁻¹) := by group
  calc z = N.x⁻¹ * (N.x * z * N.x⁻¹) * N.x := by group
    _ = 1 := by rw [h1]; group

theorem OutCtx.mem_Kg_of_comm
    (hAF : OutAutAll) (c : OutCtx N t zK R) {g i e : G}
    (hg : g⁻¹ * t * g = i) (he : i * e = e * i) (hodd : Odd (orderOf e)) :
    e ∈ CFSG.conjugate N.K g := by
  rw [BenderBranch.mem_conjugate_iff]
  have hGt : g * e * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g * e * g⁻¹) * t = g * (e * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * (e * i) * g⁻¹ := by rw [hg]
      _ = g * (i * e) * g⁻¹ := by rw [← he]
      _ = g * ((g⁻¹ * t * g) * e) * g⁻¹ := by rw [hg]
      _ = t * (g * e * g⁻¹) := by group
  have hord : orderOf (g * e * g⁻¹) = orderOf e :=
    orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective e
  exact c.lv.odd_mem_K hAF c.par c.typ c.ne c.comm hGt (by rw [hord]; exact hodd)

theorem OutCtx.conjugate_K_eq_of_le
    (hAF : OutAutAll) (c : OutCtx N t zK R) {h' : G}
    (hle : CFSG.conjugate N.K h' ≤ Subgroup.centralizer ({t} : Set G)) :
    CFSG.conjugate N.K h' = N.K := by
  have hKh : IsL2pType ↥(CFSG.conjugate N.K h') := isL2pType_conjugate h' c.typ
  have hd := l2pFacts ↥(CFSG.conjugate N.K h') hKh
  have hsimple : IsSimpleGroup ↥(CFSG.conjugate N.K h') := hd.simple
  have hnc : ∃ a ∈ CFSG.conjugate N.K h', ∃ b ∈ CFSG.conjugate N.K h', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hd.nonabelian
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  have hle' := c.lv.simple_le_K hAF c.par c.typ c.ne c.comm hle hsimple hnc
  exact Subgroup.eq_of_le_of_card_ge hle' (BenderBranch.card_conjugate _ _).ge

theorem OutCtx.inner_inner_mem (c : OutCtx N t zK R) {i : G} (hK : InnerOn N.K i)
    (hKx : InnerOn (CFSG.conjugate N.K N.x) i) : i ∈ N.Kplus := by
  obtain ⟨k, hk, hkv⟩ := hK
  obtain ⟨k', hk', hk'u⟩ := hKx
  have hkk' : k * k' = k' * k := c.comm k hk k' hk'
  set y : G := (k * k')⁻¹ * i with hy
  have hyY : y ∈ N.Yc := by
    rw [Notation25.mem_Yc]
    intro w hw
    have hle : N.Kplus ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le ?_ ?_
      · intro v hv
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hkv v hv
        have h2 : v * k' = k' * v := c.comm v hv k' hk'
        have h3 : v * k'⁻¹ = k'⁻¹ * v := by
          calc v * k'⁻¹ = k'⁻¹ * (k' * v) * k'⁻¹ := by group
            _ = k'⁻¹ * (v * k') * k'⁻¹ := by rw [h2]
            _ = k'⁻¹ * v := by group
        have h4 : i * v = (k * v * k⁻¹) * i := by
          calc i * v = (i * v * i⁻¹) * i := by group
            _ = (k * v * k⁻¹) * i := by rw [h1]
        calc v * y = v * ((k * k')⁻¹ * i) := by rw [hy]
          _ = ((k * k')⁻¹ * (k * v * k⁻¹) ) * i := by
            have : v * (k * k')⁻¹ = (k * k')⁻¹ * (k * v * k⁻¹) := by
              calc v * (k * k')⁻¹ = v * (k'⁻¹ * k⁻¹) := by group
                _ = (v * k'⁻¹) * k⁻¹ := by group
                _ = (k'⁻¹ * v) * k⁻¹ := by rw [h3]
                _ = k'⁻¹ * k⁻¹ * (k * v * k⁻¹) := by group
                _ = (k * k')⁻¹ * (k * v * k⁻¹) := by group
            calc v * ((k * k')⁻¹ * i) = (v * (k * k')⁻¹) * i := by group
              _ = ((k * k')⁻¹ * (k * v * k⁻¹)) * i := by rw [this]
          _ = (k * k')⁻¹ * (i * v) := by rw [h4]; group
          _ = y * v := by rw [hy, mul_assoc]
      · intro u hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hk'u u hu
        have h2 : k * u = u * k := c.comm k hk u hu
        have h3 : k⁻¹ * u = u * k⁻¹ := by
          calc k⁻¹ * u = k⁻¹ * (u * k) * k⁻¹ := by group
            _ = k⁻¹ * (k * u) * k⁻¹ := by rw [h2]
            _ = u * k⁻¹ := by group
        have h4 : i * u = (k' * u * k'⁻¹) * i := by
          calc i * u = (i * u * i⁻¹) * i := by group
            _ = (k' * u * k'⁻¹) * i := by rw [h1]
        calc u * y = u * ((k * k')⁻¹ * i) := by rw [hy]
          _ = ((k * k')⁻¹ * (k' * u * k'⁻¹)) * i := by
            have : u * (k * k')⁻¹ = (k * k')⁻¹ * (k' * u * k'⁻¹) := by
              have hkk'' : (k * k')⁻¹ = k⁻¹ * k'⁻¹ := by
                calc (k * k')⁻¹ = (k' * k)⁻¹ := by rw [hkk']
                  _ = k⁻¹ * k'⁻¹ := by group
              calc u * (k * k')⁻¹ = u * (k⁻¹ * k'⁻¹) := by rw [hkk'']
                _ = (u * k⁻¹) * k'⁻¹ := by group
                _ = (k⁻¹ * u) * k'⁻¹ := by rw [h3]
                _ = k⁻¹ * k'⁻¹ * (k' * u * k'⁻¹) := by group
                _ = (k * k')⁻¹ * (k' * u * k'⁻¹) := by rw [hkk'']
            calc u * ((k * k')⁻¹ * i) = (u * (k * k')⁻¹) * i := by group
              _ = ((k * k')⁻¹ * (k' * u * k'⁻¹)) * i := by rw [this]
          _ = (k * k')⁻¹ * (i * u) := by rw [h4]; group
          _ = y * u := by rw [hy, mul_assoc]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hy1 : y = 1 := by
    rw [c.lv.Yc_eq_bot c.par c.comm, Subgroup.mem_bot] at hyY
    exact hyY
  have hi : i = k * k' := by
    calc i = (k * k') * ((k * k')⁻¹ * i) := by group
      _ = k * k' := by rw [← hy, hy1, mul_one]
  rw [hi]
  exact N.Kplus.mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hk')

theorem OutCtx.swap_false
    (hAF : OutAutAll) (c : OutCtx N t zK R) {i g : G} (hi2 : i * i = 1)
    (hswap : CFSG.conjugate N.K i = CFSG.conjugate N.K N.x) (hg : g⁻¹ * t * g = i) : False := by
  have hf := c.lv.facts2511
  have hiK : ∀ k ∈ N.K, i * k * i⁻¹ ∈ CFSG.conjugate N.K N.x := by
    intro k hk
    rw [← hswap, BenderBranch.mem_conjugate_iff]
    have : i * (i * k * i⁻¹) * i⁻¹ = k := by
      calc i * (i * k * i⁻¹) * i⁻¹ = (i * i) * k * (i * i)⁻¹ := by group
        _ = k := by rw [hi2]; group
    rw [this]; exact hk
  have hcm : ∀ a b : ↥N.K, (b : G) * (i * (a : G) * i⁻¹) = (i * (a : G) * i⁻¹) * b :=
    fun a b => c.comm b b.2 _ (hiK a a.2)
  let μ : ↥N.K →* G := MonoidHom.mk' (fun k => (k : G) * (i * (k : G) * i⁻¹)) (by
    intro a b
    show ((a * b : ↥N.K) : G) * (i * ((a * b : ↥N.K) : G) * i⁻¹) =
      ((a : G) * (i * (a : G) * i⁻¹)) * ((b : G) * (i * (b : G) * i⁻¹))
    have hab : ((a * b : ↥N.K) : G) = (a : G) * (b : G) := rfl
    rw [hab]
    calc (a : G) * (b : G) * (i * ((a : G) * (b : G)) * i⁻¹)
        = (a : G) * (b : G) * ((i * (a : G) * i⁻¹) * (i * (b : G) * i⁻¹)) := by group
      _ = (a : G) * ((b : G) * (i * (a : G) * i⁻¹)) * (i * (b : G) * i⁻¹) := by group
      _ = (a : G) * ((i * (a : G) * i⁻¹) * (b : G)) * (i * (b : G) * i⁻¹) := by rw [hcm a b]
      _ = ((a : G) * (i * (a : G) * i⁻¹)) * ((b : G) * (i * (b : G) * i⁻¹)) := by group)
  have hμ : ∀ k : ↥N.K, μ k = (k : G) * (i * (k : G) * i⁻¹) := fun k => rfl
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : (k : G) * (i * (k : G) * i⁻¹) = 1 := hk
    have hkx : (k : G) ∈ CFSG.conjugate N.K N.x := by
      have : (k : G) = (i * (k : G) * i⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hk'
      rw [this]
      exact (CFSG.conjugate N.K N.x).inv_mem (hiK k k.2)
    have h1 : (k : G) ∈ N.K ⊓ CFSG.conjugate N.K N.x := ⟨k.2, hkx⟩
    rw [c.lv.K_inf_conjugate_eq_bot (Lv2520.K_le_normalizer_Kx_of_commute (N := N) c.comm),
      Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  let φ : ↥N.K →* G := (MulAut.conj g).toMonoidHom.comp μ
  have hφinj : Function.Injective φ := (MulAut.conj g).injective.comp hμinj
  have hφ : ∀ k : ↥N.K, φ k = g * ((k : G) * (i * (k : G) * i⁻¹)) * g⁻¹ := fun k => rfl
  have hφt : φ.range ≤ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hφ]
    have h1 : i * ((k : G) * (i * (k : G) * i⁻¹)) * i⁻¹ = (k : G) * (i * (k : G) * i⁻¹) := by
      calc i * ((k : G) * (i * (k : G) * i⁻¹)) * i⁻¹
          = (i * (k : G) * i⁻¹) * (i * (i * (k : G) * i⁻¹) * i⁻¹) := by group
        _ = (i * (k : G) * i⁻¹) * (k : G) := by
          have : i * (i * (k : G) * i⁻¹) * i⁻¹ = (k : G) := by
            calc i * (i * (k : G) * i⁻¹) * i⁻¹ = (i * i) * (k : G) * (i * i)⁻¹ := by group
              _ = k := by rw [hi2]; group
          rw [this]
        _ = (k : G) * (i * (k : G) * i⁻¹) := (hcm k k).symm
    have h2 : ((k : G) * (i * (k : G) * i⁻¹)) * i = i * ((k : G) * (i * (k : G) * i⁻¹)) := by
      calc ((k : G) * (i * (k : G) * i⁻¹)) * i
          = (i * ((k : G) * (i * (k : G) * i⁻¹)) * i⁻¹) * i := by rw [h1]
        _ = i * ((k : G) * (i * (k : G) * i⁻¹)) := by group
    have ht : t = g * i * g⁻¹ := by rw [← hg]; group
    rw [ht]
    calc g * ((k : G) * (i * (k : G) * i⁻¹)) * g⁻¹ * (g * i * g⁻¹)
        = g * (((k : G) * (i * (k : G) * i⁻¹)) * i) * g⁻¹ := by group
      _ = g * (i * ((k : G) * (i * (k : G) * i⁻¹))) * g⁻¹ := by rw [h2]
      _ = g * i * g⁻¹ * (g * ((k : G) * (i * (k : G) * i⁻¹)) * g⁻¹) := by group
  have hsimple : IsSimpleGroup ↥φ.range := by
    have e : ↥N.K ≃* ↥φ.range := MonoidHom.ofInjective hφinj
    have : IsSimpleGroup ↥N.K := c.lv.facts258.simple
    exact e.symm.isSimpleGroup
  have hnc : ∃ a ∈ φ.range, ∃ b ∈ φ.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := (l2pFacts ↥N.K c.typ).nonabelian
    refine ⟨φ a, ⟨a, rfl⟩, φ b, ⟨b, rfl⟩, fun h => hab ?_⟩
    apply hφinj
    rw [map_mul, map_mul]
    exact h
  have hLK : φ.range ≤ N.K := c.lv.simple_le_K hAF c.par c.typ c.ne c.comm hφt hsimple hnc
  have hzKK : zK ∈ N.K := c.zK_mem
  have hzK2 : zK * zK = 1 := hf.zK_sq
  have hzK1 : zK ≠ 1 := c.lv.zK_ne_one
  have hbKx : i * zK * i⁻¹ ∈ CFSG.conjugate N.K N.x := hiK zK hzKK
  have hb2 : (i * zK * i⁻¹) * (i * zK * i⁻¹) = 1 := by
    calc (i * zK * i⁻¹) * (i * zK * i⁻¹) = i * (zK * zK) * i⁻¹ := by group
      _ = 1 := by rw [hzK2]; group
  have hb1 : i * zK * i⁻¹ ≠ 1 := by
    intro h1
    apply hzK1
    calc zK = i⁻¹ * (i * zK * i⁻¹) * i := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨c', hc'⟩ := c.lv.diag_conj_z c.par c.fam c.comm hzKK hbKx hzK1 hb1 hzK2 hb2
  have hu'L : g * (zK * (i * zK * i⁻¹)) * g⁻¹ ∈ φ.range := ⟨⟨zK, hzKK⟩, rfl⟩
  have hu'K : g * (zK * (i * zK * i⁻¹)) * g⁻¹ ∈ N.K := hLK hu'L
  have hcz : zK * (i * zK * i⁻¹) = (i * zK * i⁻¹) * zK := c.comm zK hzKK _ hbKx
  have hu'2 : (g * (zK * (i * zK * i⁻¹)) * g⁻¹) * (g * (zK * (i * zK * i⁻¹)) * g⁻¹) = 1 := by
    have h1 : (zK * (i * zK * i⁻¹)) * (zK * (i * zK * i⁻¹)) = 1 := by
      calc (zK * (i * zK * i⁻¹)) * (zK * (i * zK * i⁻¹))
          = zK * ((i * zK * i⁻¹) * zK) * (i * zK * i⁻¹) := by group
        _ = zK * (zK * (i * zK * i⁻¹)) * (i * zK * i⁻¹) := by rw [hcz]
        _ = (zK * zK) * ((i * zK * i⁻¹) * (i * zK * i⁻¹)) := by group
        _ = 1 := by rw [hzK2, hb2]; group
    calc (g * (zK * (i * zK * i⁻¹)) * g⁻¹) * (g * (zK * (i * zK * i⁻¹)) * g⁻¹)
        = g * ((zK * (i * zK * i⁻¹)) * (zK * (i * zK * i⁻¹))) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hu'1 : g * (zK * (i * zK * i⁻¹)) * g⁻¹ ≠ 1 := by
    intro h1
    have h2 : zK * (i * zK * i⁻¹) = 1 := by
      calc zK * (i * zK * i⁻¹) = g⁻¹ * (g * (zK * (i * zK * i⁻¹)) * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have h3 : zK = (i * zK * i⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h2
    have h4 : zK ∈ N.K ⊓ CFSG.conjugate N.K N.x := by
      refine ⟨hzKK, ?_⟩
      rw [h3]
      exact (CFSG.conjugate N.K N.x).inv_mem hbKx
    rw [c.lv.K_inf_conjugate_eq_bot (Lv2520.K_le_normalizer_Kx_of_commute (N := N) c.comm),
      Subgroup.mem_bot] at h4
    exact hzK1 h4
  obtain ⟨m, -, hmu⟩ := c.lv.involution_conj_t c.par c.fam c.comm (Or.inl hu'K) hu'1 hu'2
  have e1 : g⁻¹ * (g * (zK * (i * zK * i⁻¹)) * g⁻¹) * g = zK * (i * zK * i⁻¹) := by group
  have e2 : c'⁻¹ * (zK * (i * zK * i⁻¹)) * c' = t * zK := by rw [hc']; group
  apply c.par.not_conj (m * g * c')
  calc (m * g * c')⁻¹ * t * (m * g * c')
      = c'⁻¹ * (g⁻¹ * (m⁻¹ * t * m) * g) * c' := by group
    _ = c'⁻¹ * (g⁻¹ * (g * (zK * (i * zK * i⁻¹)) * g⁻¹) * g) * c' := by rw [← hmu]
    _ = c'⁻¹ * (zK * (i * zK * i⁻¹)) * c' := by rw [e1]
    _ = t * zK := e2


theorem Lv2520.zK_mem_commutator_SK (h : Lv2520 N t zK) {R : Subgroup ↥(autOn N.S N.K)}
    (hR : DS.DSData R) : zK ∈ ⁅N.SK, N.SK⁆ := by
  have hSB := h.sBar hR
  have h258 := h.facts258
  have hf := h.facts2511
  have hzKS : zK ∈ N.S := hf.zK_mem_center.1
  have hQA : N.SK ⊓ N.SC = ⊥ := h.SK_inf_SC
  obtain ⟨ρ, hρQ, hρR, hρ⟩ := hSB.exists_sq_ne_one N.SK_le_S hQA h258.eight_le_card_SK
  obtain ⟨w, hwc, hwz⟩ := hSB.exists_mem_commutator N.SK_le_S hQA (h.not_SK_le_Rt hR) hρQ hρR hρ
  have hπz : actS N.K N.S h.S_le_normalizer zK = hSB.ds.z := h.pi_zK hR
  have hwSK : w ∈ N.SK := commutator_le_self _ hwc
  have hwS : w ∈ N.S := N.SK_le_S hwSK
  have hmem : w⁻¹ * zK ∈ N.SC := (hSB.pi_eq_iff hwS hzKS).mp (hwz.trans hπz.symm)
  have hK : w⁻¹ * zK ∈ N.K :=
    N.K.mul_mem (N.K.inv_mem (N.SK_le_K hwSK)) (h.hK0 ▸ hf.zK_mem)
  have hzw : zK = w := (inv_mul_eq_one.mp (h.K_inf_SC_eq_bot_mem hK hmem)).symm
  rw [hzw]
  exact hwc

omit [Finite G] in
theorem mem_normalizer_conj_of_mem_normalizer_conjugate {A : Subgroup G} {x i : G}
    (h : i ∈ Subgroup.normalizer ((CFSG.conjugate A x : Subgroup G) : Set G)) :
    x * i * x⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have h1 := Subgroup.mem_normalizer_iff.mp h (x⁻¹ * v * x)
  try simp only [SetLike.mem_coe] at h1
  rw [BenderBranch.mem_conjugate_iff, BenderBranch.mem_conjugate_iff] at h1
  have e1 : x * (x⁻¹ * v * x) * x⁻¹ = v := by group
  have e2 : x * (i * (x⁻¹ * v * x) * i⁻¹) * x⁻¹ = (x * i * x⁻¹) * v * (x * i * x⁻¹)⁻¹ := by
    group
  rwa [e1, e2] at h1

omit [Finite G] in
theorem mem_centralizer_t_of_comm {t g i e : G} (hg : g⁻¹ * t * g = i) (he : i * e = e * i) :
    g * e * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (g * e * g⁻¹) * t = g * (e * (g⁻¹ * t * g)) * g⁻¹ := by group
    _ = g * (e * i) * g⁻¹ := by rw [hg]
    _ = g * (i * e) * g⁻¹ := by rw [← he]
    _ = g * ((g⁻¹ * t * g) * e) * g⁻¹ := by rw [hg]
    _ = t * (g * e * g⁻¹) := by group

theorem OutCtx.mem_normalizer_Kg (c : OutCtx N t zK R) {g i w : G} (hg : g⁻¹ * t * g = i)
    (hw : i * w = w * i) :
    w ∈ Subgroup.normalizer ((CFSG.conjugate N.K g : Subgroup G) : Set G) := by
  have hGt := mem_centralizer_t_of_comm hg hw
  have hN : g * w * g⁻¹ ∈ Subgroup.normalizer (N.K : Set G) :=
    c.lv.centralizer_t_le_normalizer hGt
  rw [Subgroup.mem_normalizer_iff]
  intro v
  try simp only [SetLike.mem_coe]
  rw [BenderBranch.mem_conjugate_iff, BenderBranch.mem_conjugate_iff]
  have h1 := Subgroup.mem_normalizer_iff.mp hN (g * v * g⁻¹)
  have e : g * (w * v * w⁻¹) * g⁻¹ = (g * w * g⁻¹) * (g * v * g⁻¹) * (g * w * g⁻¹)⁻¹ := by group
  rw [e]
  exact h1

theorem OutCtx.Kx_le_normalizer_K (c : OutCtx N t zK R) :
    CFSG.conjugate N.K N.x ≤ Subgroup.normalizer (N.K : Set G) := by
  intro u hu
  have h1 : ∀ w ∈ CFSG.conjugate N.K N.x, ∀ y ∈ N.K, w * y * w⁻¹ = y := by
    intro w hw y hy
    have := c.comm y hy w hw
    calc w * y * w⁻¹ = (w * y) * w⁻¹ := rfl
      _ = (y * w) * w⁻¹ := by rw [this]
      _ = y := by group
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    rw [h1 u hu v hv]
    exact hv
  · intro hv
    have h2 := h1 u⁻¹ ((CFSG.conjugate N.K N.x).inv_mem hu) (u * v * u⁻¹) hv
    have e : u⁻¹ * (u * v * u⁻¹) * u⁻¹⁻¹ = v := by group
    rw [e] at h2
    rw [h2]
    exact hv

end Ctx

section Core

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G} {R : Subgroup ↥(autOn N.S N.K)}

theorem OutCtx.core_OO
    (hAF : OutAutAll) (c : OutCtx N t zK R) {i g : G}
    (hiN : i ∈ Subgroup.normalizer (N.K : Set G))
    (hi'N : N.x * i * N.x⁻¹ ∈ Subgroup.normalizer (N.K : Set G))
    (hi2 : i * i = 1) (hg : g⁻¹ * t * g = i)
    (hout : ¬ InnerOn N.K i) (hout' : ¬ InnerOn N.K (N.x * i * N.x⁻¹)) : False := by
  have hi'2 : (N.x * i * N.x⁻¹) * (N.x * i * N.x⁻¹) = 1 := by
    calc (N.x * i * N.x⁻¹) * (N.x * i * N.x⁻¹) = N.x * (i * i) * N.x⁻¹ := by group
      _ = 1 := by rw [hi2]; group
  obtain ⟨a, haK, q, hq, hq2, haq, hia⟩ := exists_odd_fixed c.typ hiN hi2 hout
  have hq1 : Odd q := hq.odd_of_ne_two hq2
  have hF := hAF ↥N.K c.typ
  obtain ⟨φ, hφ⟩ := hF.outer_conj (actA N.K i hiN) (actA N.K (N.x * i * N.x⁻¹) hi'N)
    (actA_mul_self N.K hiN hi2) (actA_mul_self N.K hi'N hi'2)
    (fun h => hout ((actA_mem_innerAut_iff N.K hiN).mp h))
    (fun h => hout' ((actA_mem_innerAut_iff N.K hi'N).mp h))
  have hαa : actA N.K i hiN ⟨a, haK⟩ = ⟨a, haK⟩ := by
    apply Subtype.ext
    rw [actA_apply]
    exact hia
  have ha'q : orderOf (⟨a, haK⟩ : ↥N.K) = q := by
    rw [← Subgroup.orderOf_coe]
    exact haq
  have hβb : actA N.K (N.x * i * N.x⁻¹) hi'N (φ ⟨a, haK⟩) = φ ⟨a, haK⟩ := by
    rw [← hφ]
    simp [hαa]
  have hb₀q : orderOf (φ ⟨a, haK⟩) = q := by
    rw [MulEquiv.orderOf_eq]
    exact ha'q
  have hb₀fix : (N.x * i * N.x⁻¹) * ((φ ⟨a, haK⟩ : ↥N.K) : G) =
      ((φ ⟨a, haK⟩ : ↥N.K) : G) * (N.x * i * N.x⁻¹) := by
    have h1 := congrArg Subtype.val hβb
    rw [actA_apply] at h1
    calc (N.x * i * N.x⁻¹) * ((φ ⟨a, haK⟩ : ↥N.K) : G)
        = ((N.x * i * N.x⁻¹) * ((φ ⟨a, haK⟩ : ↥N.K) : G) * (N.x * i * N.x⁻¹)⁻¹) *
            (N.x * i * N.x⁻¹) := by group
      _ = ((φ ⟨a, haK⟩ : ↥N.K) : G) * (N.x * i * N.x⁻¹) := by rw [h1]
  set b : G := N.x⁻¹ * ((φ ⟨a, haK⟩ : ↥N.K) : G) * N.x with hb
  have hbKx : b ∈ CFSG.conjugate N.K N.x := by
    rw [BenderBranch.mem_conjugate_iff]
    have : N.x * b * N.x⁻¹ = ((φ ⟨a, haK⟩ : ↥N.K) : G) := by rw [hb]; group
    rw [this]
    exact (φ ⟨a, haK⟩).2
  have hbq : orderOf b = q := by
    have h1 : orderOf ((MulAut.conj N.x⁻¹).toMonoidHom ((φ ⟨a, haK⟩ : ↥N.K) : G)) =
        orderOf ((φ ⟨a, haK⟩ : ↥N.K) : G) :=
      orderOf_injective _ (MulAut.conj N.x⁻¹).injective _
    have h2 : (MulAut.conj N.x⁻¹).toMonoidHom ((φ ⟨a, haK⟩ : ↥N.K) : G) = b := by
      simp [hb]
    rw [h2, Subgroup.orderOf_coe] at h1
    rw [h1]
    exact hb₀q
  have hib : i * b = b * i := by
    calc i * b = N.x⁻¹ * ((N.x * i * N.x⁻¹) * ((φ ⟨a, haK⟩ : ↥N.K) : G)) * N.x := by
          rw [hb]; group
      _ = N.x⁻¹ * (((φ ⟨a, haK⟩ : ↥N.K) : G) * (N.x * i * N.x⁻¹)) * N.x := by rw [hb₀fix]
      _ = b * i := by rw [hb]; group
  have hiaC : i * a = a * i := by
    calc i * a = (i * a * i⁻¹) * i := by group
      _ = a * i := by rw [hia]
  have haKg : a ∈ CFSG.conjugate N.K g :=
    c.mem_Kg_of_comm hAF hg hiaC (by rw [haq]; exact hq1)
  have hbKg : b ∈ CFSG.conjugate N.K g :=
    c.mem_Kg_of_comm hAF hg hib (by rw [hbq]; exact hq1)
  have hKg : IsL2pType ↥(CFSG.conjugate N.K g) := isL2pType_conjugate g c.typ
  have hX := hAF _ hKg
  have hab : a * b = b * a := c.comm a haK b hbKx
  have hmem := hX.odd_pair q hq hq2 ⟨a, haKg⟩ ⟨b, hbKg⟩
    (by rw [← Subgroup.orderOf_coe]; exact haq) (by rw [← Subgroup.orderOf_coe]; exact hbq)
    (Subtype.ext hab)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hbK : b ∈ N.K := by
    have h1 : (a : G) ^ n = b := by simpa using congrArg Subtype.val hn
    rw [← h1]
    exact N.K.zpow_mem haK n
  have h0 : b ∈ N.K ⊓ CFSG.conjugate N.K N.x := ⟨hbK, hbKx⟩
  rw [c.lv.K_inf_conjugate_eq_bot (Lv2520.K_le_normalizer_Kx_of_commute (N := N) c.comm),
    Subgroup.mem_bot] at h0
  rw [h0, orderOf_one] at hbq
  exact hq.one_lt.ne hbq

theorem OutCtx.core_OI0
    (hAF : OutAutAll) (c : OutCtx N t zK R) {j g : G}
    (hjN : j ∈ Subgroup.normalizer (N.K : Set G)) (hj2 : j * j = 1) (hg : g⁻¹ * t * g = j)
    (hyC : ∀ u ∈ CFSG.conjugate N.K N.x, j * u = u * j) (hout : ¬ InnerOn N.K j) : False := by
  obtain ⟨a, haK, q, hq, hq2, haq, hja⟩ := exists_odd_fixed c.typ hjN hj2 hout
  have hq1 : Odd q := hq.odd_of_ne_two hq2
  have hjaC : j * a = a * j := by
    calc j * a = (j * a * j⁻¹) * j := by group
      _ = a * j := by rw [hja]
  have haKg : a ∈ CFSG.conjugate N.K g :=
    c.mem_Kg_of_comm hAF hg hjaC (by rw [haq]; exact hq1)
  have hL : CFSG.conjugate N.K (N.x * g⁻¹) ≤ Subgroup.centralizer ({t} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hu : g⁻¹ * v * g ∈ CFSG.conjugate N.K N.x := by
      rw [BenderBranch.mem_conjugate_iff]
      rw [BenderBranch.mem_conjugate_iff] at hv
      have e : N.x * g⁻¹ * v * (N.x * g⁻¹)⁻¹ = N.x * (g⁻¹ * v * g) * N.x⁻¹ := by group
      rwa [e] at hv
    have h1 := hyC _ hu
    have ht : t = g * j * g⁻¹ := by rw [← hg]; group
    rw [ht]
    calc v * (g * j * g⁻¹) = g * ((g⁻¹ * v * g) * j) * g⁻¹ := by group
      _ = g * (j * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = (g * j * g⁻¹) * v := by group
  have hLeq := c.conjugate_K_eq_of_le hAF hL
  have hKxg : CFSG.conjugate N.K N.x = CFSG.conjugate N.K g := by
    calc CFSG.conjugate N.K N.x = CFSG.conjugate N.K (N.x * g⁻¹ * g) := by
          rw [inv_mul_cancel_right]
      _ = CFSG.conjugate (CFSG.conjugate N.K (N.x * g⁻¹)) g :=
          (BenderBranch.conjugate_conjugate _ _ _).symm
      _ = CFSG.conjugate N.K g := by rw [hLeq]
  have haKx : a ∈ CFSG.conjugate N.K N.x := by rw [hKxg]; exact haKg
  have h0 : a ∈ N.K ⊓ CFSG.conjugate N.K N.x := ⟨haK, haKx⟩
  rw [c.lv.K_inf_conjugate_eq_bot (Lv2520.K_le_normalizer_Kx_of_commute (N := N) c.comm),
    Subgroup.mem_bot] at h0
  rw [h0, orderOf_one] at haq
  exact hq.one_lt.ne haq

theorem OutCtx.core_OI1
    (hAF : OutAutAll) (c : OutCtx N t zK R) {y g : G}
    (hyN : y ∈ Subgroup.normalizer (N.K : Set G)) (hy2 : y * y = 1)
    (hyC : ∀ u ∈ CFSG.conjugate N.K N.x, y * u = u * y) (hg : g⁻¹ * t * g = t * y)
    (hout : ¬ InnerOn N.K y) : False := by
  have hf := c.lv.facts2511
  have htKx := c.t_mem_Kx
  obtain ⟨a, haK, q, hq, hq2, haq, hya⟩ := exists_odd_fixed c.typ hyN hy2 hout
  have hq1 : Odd q := hq.odd_of_ne_two hq2
  have hta : t * a = a * t := (c.comm a haK t htKx).symm
  have hyaC : y * a = a * y := by
    calc y * a = (y * a * y⁻¹) * y := by group
      _ = a * y := by rw [hya]
  have hia : (t * y) * a = a * (t * y) := by
    calc (t * y) * a = t * (y * a) := by group
      _ = t * (a * y) := by rw [hyaC]
      _ = (t * a) * y := by group
      _ = (a * t) * y := by rw [hta]
      _ = a * (t * y) := by group
  have haKg : a ∈ CFSG.conjugate N.K g := c.mem_Kg_of_comm hAF hg hia (by rw [haq]; exact hq1)
  have hWS : CFSG.conjugate N.SK N.x ≤ N.S := c.lv.conjugate_SK_le_S
  have hWKx : CFSG.conjugate N.SK N.x ≤ CFSG.conjugate N.K N.x :=
    BenderBranch.conjugate_mono N.SK_le_K N.x
  have hW2 : IsPGroup 2 ↥(CFSG.conjugate N.SK N.x) := N.tuple.sylow.isPGroup.to_le hWS
  have hWi : ∀ w ∈ CFSG.conjugate N.SK N.x, (t * y) * w = w * (t * y) := by
    intro w hw
    have h1 : w * t = t * w := Subgroup.mem_centralizer_iff.mp hf.t_mem_center.2 w (hWS hw)
    have h2 : y * w = w * y := hyC w (hWKx hw)
    calc (t * y) * w = t * (y * w) := by group
      _ = t * (w * y) := by rw [h2]
      _ = (t * w) * y := by group
      _ = (w * t) * y := by rw [h1]
      _ = w * (t * y) := by group
  have hWN : CFSG.conjugate N.SK N.x ≤
      Subgroup.normalizer ((CFSG.conjugate N.K g : Subgroup G) : Set G) :=
    fun w hw => c.mem_normalizer_Kg (g := g) (i := t * y) hg (hWi w hw)
  have hWa : ∀ w ∈ CFSG.conjugate N.SK N.x, w * a = a * w :=
    fun w hw => (c.comm a haK w (hWKx hw)).symm
  have hKgtype : IsL2pType ↥(CFSG.conjugate N.K g) := isL2pType_conjugate g c.typ
  have hcomm := commutator_le_centralizer_of_odd_fixed hAF hKgtype haKg hq hq2 haq hW2 hWN hWa
  have htW : t ∈ ⁅CFSG.conjugate N.SK N.x, CFSG.conjugate N.SK N.x⁆ := by
    have h1 := c.lv.zK_mem_commutator_SK c.par.ds
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj N.x⁻¹).toMonoidHom h1
    rw [Subgroup.map_commutator] at h2
    have e : (MulAut.conj N.x⁻¹).toMonoidHom zK = t := by
      have := c.xinv_zK_x
      simpa [MulAut.conj_apply] using this
    rw [e] at h2
    exact h2
  have htC : t ∈ Subgroup.centralizer ((CFSG.conjugate N.K g : Subgroup G) : Set G) := hcomm htW
  have hKgle : CFSG.conjugate N.K g ≤ Subgroup.centralizer ({t} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp htC v hv
  have hKgeq := c.conjugate_K_eq_of_le hAF hKgle
  have hiK : ∀ v ∈ N.K, (t * y) * v = v * (t * y) := by
    intro v hv
    have hvKg : v ∈ CFSG.conjugate N.K g := by rw [hKgeq]; exact hv
    rw [BenderBranch.mem_conjugate_iff] at hvKg
    have h1 : t * (g * v * g⁻¹) = (g * v * g⁻¹) * t := (c.comm _ hvKg t htKx).symm
    rw [← hg]
    calc g⁻¹ * t * g * v = g⁻¹ * (t * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * v * g⁻¹) * t) * g := by rw [h1]
      _ = v * (g⁻¹ * t * g) := by group
  apply hout
  refine ⟨1, N.K.one_mem, fun v hv => ?_⟩
  have h1 := hiK v hv
  have h2 : t * v = v * t := (c.comm v hv t htKx).symm
  have h3 : t⁻¹ * v = v * t⁻¹ := by
    calc t⁻¹ * v = t⁻¹ * (v * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * v) * t⁻¹ := by rw [← h2]
      _ = v * t⁻¹ := by group
  have h4 : y * v = v * y := by
    calc y * v = t⁻¹ * ((t * y) * v) := by group
      _ = t⁻¹ * (v * (t * y)) := by rw [h1]
      _ = (t⁻¹ * v) * (t * y) := by group
      _ = (v * t⁻¹) * (t * y) := by rw [h3]
      _ = v * y := by group
  rw [one_mul, inv_one, mul_one]
  calc y * v * y⁻¹ = (v * y) * y⁻¹ := by rw [h4]
    _ = v := by group

theorem OutCtx.core_OI
    (hAF : OutAutAll) (c : OutCtx N t zK R) {j g : G}
    (hjN : j ∈ Subgroup.normalizer (N.K : Set G)) (hj2 : j * j = 1) (hg : g⁻¹ * t * g = j)
    (hout : ¬ InnerOn N.K j) (hin : InnerOn (CFSG.conjugate N.K N.x) j) : False := by
  obtain ⟨k', hk'Kx, hk'⟩ := hin
  have hKxN := c.Kx_le_normalizer_K
  set y : G := k'⁻¹ * j with hy
  have hjky : j = k' * y := by rw [hy]; group
  have hyC : ∀ u ∈ CFSG.conjugate N.K N.x, y * u = u * y := by
    intro u hu
    have h1 := hk' u hu
    calc y * u = k'⁻¹ * (j * u * j⁻¹) * j := by rw [hy]; group
      _ = k'⁻¹ * (k' * u * k'⁻¹) * j := by rw [h1]
      _ = u * (k'⁻¹ * j) := by group
      _ = u * y := by rw [hy]
  have hk'y : k' * y = y * k' := (hyC k' hk'Kx).symm
  have hsq : (k' * k') * (y * y) = 1 := by
    calc (k' * k') * (y * y) = k' * (k' * y) * y := by group
      _ = k' * (y * k') * y := by rw [hk'y]
      _ = (k' * y) * (k' * y) := by group
      _ = j * j := by rw [← hjky]
      _ = 1 := hj2
  have hyyKx : y * y ∈ CFSG.conjugate N.K N.x := by
    have : y * y = (k' * k')⁻¹ := eq_inv_of_mul_eq_one_right hsq
    rw [this]
    exact (CFSG.conjugate N.K N.x).inv_mem ((CFSG.conjugate N.K N.x).mul_mem hk'Kx hk'Kx)
  have hyy1 : y * y = 1 := by
    refine c.centerless_Kx hyyKx fun u hu => ?_
    have h1 := hyC u hu
    calc y * y * u = y * (y * u) := by group
      _ = y * (u * y) := by rw [h1]
      _ = (y * u) * y := by group
      _ = (u * y) * y := by rw [h1]
      _ = u * (y * y) := by group
  have hk'2 : k' * k' = 1 := by
    rw [hyy1, mul_one] at hsq
    exact hsq
  by_cases hk'1 : k' = 1
  ·
    refine c.core_OI0 hAF hjN hj2 hg (fun u hu => ?_) hout
    have h1 := hk' u hu
    rw [hk'1] at h1
    simp only [one_mul, inv_one, mul_one] at h1
    calc j * u = (j * u * j⁻¹) * j := by group
      _ = u * j := by rw [h1]
  ·
    have hKxtype : IsL2pType ↥(CFSG.conjugate N.K N.x) := isL2pType_conjugate N.x c.typ
    have hd := l2pFacts ↥(CFSG.conjugate N.K N.x) hKxtype
    have hord2 : ∀ (z : G) (hz : z ∈ CFSG.conjugate N.K N.x), z * z = 1 → z ≠ 1 →
        orderOf (⟨z, hz⟩ : ↥(CFSG.conjugate N.K N.x)) = 2 := by
      intro z hz hz2 hz1
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        show z ^ 2 = 1
        rw [pow_two]
        exact hz2
      · intro h1
        exact hz1 (congrArg Subtype.val h1)
    obtain ⟨w, hw⟩ := hd.single_class ⟨k', hk'Kx⟩ ⟨t, c.t_mem_Kx⟩
      (hord2 k' hk'Kx hk'2 hk'1) (hord2 t c.t_mem_Kx c.lv.facts2511.t_mul_t c.lv.facts2511.t_ne_one)
    have hwk : (w : G) * k' * (w : G)⁻¹ = t := by simpa using congrArg Subtype.val hw
    have hwy : (w : G) * y = y * (w : G) := (hyC w w.2).symm
    have hyN : y ∈ Subgroup.normalizer (N.K : Set G) :=
      (Subgroup.normalizer (N.K : Set G)).mul_mem
        ((Subgroup.normalizer (N.K : Set G)).inv_mem (hKxN hk'Kx)) hjN
    refine c.core_OI1 hAF (y := y) (g := g * (w : G)⁻¹) hyN hyy1 hyC ?_ ?_
    · have e1 : (g * (w : G)⁻¹)⁻¹ * t * (g * (w : G)⁻¹) =
          (w : G) * (g⁻¹ * t * g) * (w : G)⁻¹ := by group
      rw [e1, hg]
      calc (w : G) * j * (w : G)⁻¹ = (w : G) * (k' * y) * (w : G)⁻¹ := by rw [← hjky]
        _ = ((w : G) * k' * (w : G)⁻¹) * ((w : G) * y * (w : G)⁻¹) := by group
        _ = t * y := by rw [hwk, hwy]; group
    · rintro ⟨a, haK, hv⟩
      apply hout
      refine ⟨a, haK, fun v hv' => ?_⟩
      have h1 := hv v hv'
      have hyvK : y * v * y⁻¹ ∈ N.K := (Subgroup.mem_normalizer_iff.mp hyN v).mp hv'
      have hc : k' * (y * v * y⁻¹) = (y * v * y⁻¹) * k' := (c.comm _ hyvK k' hk'Kx).symm
      calc j * v * j⁻¹ = k' * (y * v * y⁻¹) * k'⁻¹ := by rw [hjky]; group
        _ = (y * v * y⁻¹) * k' * k'⁻¹ := by rw [hc]
        _ = a * v * a⁻¹ := by rw [h1]; group

theorem OutCtx.outside_false
    (hAF : OutAutAll) (c : OutCtx N t zK R) {i g : G}
    (hi : i ∈ N.Mplus) (hi2 : i * i = 1) (hiK : i ∉ N.Kplus) (hg : g⁻¹ * t * g = i) : False := by
  rcases c.lv.conj_K_eq c.comm hi with h1 | h1
  ·
    have hiN : i ∈ Subgroup.normalizer (N.K : Set G) :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mp h1
    have hiNx : i ∈ Subgroup.normalizer ((CFSG.conjugate N.K N.x : Subgroup G) : Set G) := by
      rcases c.lv.conj_Kx_eq c.comm hi with h2 | h2
      · exfalso
        apply c.ne
        have h3 : CFSG.conjugate (CFSG.conjugate N.K N.x) i = CFSG.conjugate N.K i := by
          rw [h2, h1]
        exact BenderBranch.conjugate_inj.mp h3
      · exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp h2
    have hi'N : N.x * i * N.x⁻¹ ∈ Subgroup.normalizer (N.K : Set G) :=
      mem_normalizer_conj_of_mem_normalizer_conjugate hiNx
    by_cases hα : InnerOn N.K i
    · by_cases hβ : InnerOn (CFSG.conjugate N.K N.x) i
      · exact hiK (c.inner_inner_mem hα hβ)
      ·
        have hj_out : ¬ InnerOn N.K (N.x * i * N.x⁻¹) := fun h => hβ (innerOn_conjugate.mpr h)
        have hj_in : InnerOn (CFSG.conjugate N.K N.x) (N.x * i * N.x⁻¹) := by
          rw [innerOn_conjugate]
          have e : N.x * (N.x * i * N.x⁻¹) * N.x⁻¹ = (N.x * N.x) * i * (N.x * N.x)⁻¹ := by group
          rw [e, innerOn_conj_of_mem_normalizer c.lv.x_sq_mem_normalizer]
          exact hα
        have hj2 : (N.x * i * N.x⁻¹) * (N.x * i * N.x⁻¹) = 1 := by
          calc (N.x * i * N.x⁻¹) * (N.x * i * N.x⁻¹) = N.x * (i * i) * N.x⁻¹ := by group
            _ = 1 := by rw [hi2]; group
        have hg' : (g * N.x⁻¹)⁻¹ * t * (g * N.x⁻¹) = N.x * i * N.x⁻¹ := by
          calc (g * N.x⁻¹)⁻¹ * t * (g * N.x⁻¹) = N.x * (g⁻¹ * t * g) * N.x⁻¹ := by group
            _ = N.x * i * N.x⁻¹ := by rw [hg]
        exact c.core_OI hAF hi'N hj2 hg' hj_out hj_in
    · by_cases hβ : InnerOn (CFSG.conjugate N.K N.x) i
      · exact c.core_OI hAF hiN hi2 hg hα hβ
      · exact c.core_OO hAF hiN hi'N hi2 hg hα (fun h => hβ (innerOn_conjugate.mpr h))
  · exact c.swap_false hAF hi2 h1 hg

end Core

theorem caseCOutside_of_facts
    (hAF : OutAutAll) : CaseCOutside := by
  intro G _ _ T M hs N t zK R h hfam hp hL2p _ _ hne hcomm i hi hi2 hiK g hg
  exact (OutCtx.mk h hp hfam hL2p hne hcomm).outside_false hAF hi hi2 hiK hg

end CFSG.QuasithinUnique
