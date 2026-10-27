module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NDefs

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

section Clique

variable {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}

omit [Finite F] in
theorem TightSettingN.centralizer_ne_top (S : TightSettingN F K z) {x : F} (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set F) ≠ ⊤ := by
  intro h
  apply hx
  apply S.center_trivial
  intro y
  have : y ∈ Subgroup.centralizer ({x} : Set F) := h ▸ Subgroup.mem_top y
  exact Subgroup.mem_centralizer_iff.mp this x rfl

omit [Finite F] in
theorem TightSettingN.mem_memb (S : TightSettingN F K z) {u : F} (hu : u ∈ classOf z) :
    u ∈ memb K z u :=
  (S.tight.memb hu).classical.mem

omit [Finite F] in
theorem TightSettingN.ne_one (S : TightSettingN F K z) {u : F} (hu : u ∈ classOf z) : u ≠ 1 := by
  intro h
  have := orderOf_eq_two_of_mem_classOf S.tight hu
  rw [h, orderOf_one] at this
  omega

omit [Finite F] in
theorem TightSettingN.isConjSubgroup_memb (S : TightSettingN F K z) {u : F} (hu : u ∈ classOf z) :
    IsConjSubgroup K (memb K z u) := by
  obtain ⟨g, hg⟩ := hu
  rw [memb_eq S.tight hg]
  exact isConjSubgroup_map_conj K g

omit [Finite F] in
theorem TightSettingN.commOrEq_of_le_centralizer (S : TightSettingN F K z) {x : F}
    (hx : orderOf x = 2) (hxE : IsCommProd z x) {u v : F} (hu : u ∈ classOf z)
    (hv : v ∈ classOf z) (hux : memb K z u ≤ Subgroup.centralizer ({x} : Set F))
    (hvx : memb K z v ≤ Subgroup.centralizer ({x} : Set F)) :
    CommOrEq (memb K z u) (memb K z v) :=
  S.IH x hx hxE _ _ u v (Or.inl (S.isConjSubgroup_memb hu)) (S.isConjSubgroup_memb hv)
    ((S.tight.memb hu).classical.mono hux le_top) ((S.tight.memb hv).classical.mono hvx le_top)

omit [Finite F] in
theorem TightSettingN.mem_centralizer_of_commOrEq (S : TightSettingN F K z) {u v : F}
    (hv : v ∈ classOf z) (h : CommOrEq (memb K z u) (memb K z v)) {k : F} (hk : k ∈ memb K z u) :
    k * v = v * k := by
  rcases h with h | h
  · rw [h] at hk
    exact (S.tight.memb hv).classical.mul_comm_of_mem hk
  · exact h k hk v (S.mem_memb hv)

omit [Finite F] in
theorem TightSettingN.commOrEq_trans (S : TightSettingN F K z) {u v w : F} (hu : u ∈ classOf z)
    (hv : v ∈ classOf z) (hw : w ∈ classOf z) (h1 : CommOrEq (memb K z u) (memb K z v))
    (h2 : CommOrEq (memb K z v) (memb K z w)) : CommOrEq (memb K z u) (memb K z w) := by
  have hc : ∀ {a : F}, a ∈ classOf z → CommOrEq (memb K z a) (memb K z v) →
      memb K z a ≤ Subgroup.centralizer ({v} : Set F) := fun {a} _ h k hk =>
    Subgroup.mem_centralizer_iff.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact (S.mem_centralizer_of_commOrEq hv h hk).symm)
  exact S.commOrEq_of_le_centralizer (orderOf_eq_two_of_mem_classOf S.tight hv)
    (isCommProd_of_mem_classOf hv) hu hw (hc hu h1) (hc hw h2.symm)

omit [Finite F] in
theorem TightSettingN.self_mem_Zset (S : TightSettingN F K z) : z ∈ Zset K z :=
  ⟨mem_classOf_self z, by rw [memb_self S.tight]; exact CommOrEq.refl K⟩

omit [Finite F] in
theorem TightSettingN.commOrEq_of_mem_Zset (S : TightSettingN F K z) {u v : F}
    (hu : u ∈ Zset K z) (hv : v ∈ Zset K z) : CommOrEq (memb K z u) (memb K z v) := by
  refine S.commOrEq_trans hu.1 (mem_classOf_self z) hv.1 ?_ ?_
  · rw [memb_self S.tight]; exact hu.2.symm
  · rw [memb_self S.tight]; exact hv.2

omit [Finite F] in
theorem TightSettingN.mem_centralizer_memb_of_mem_Zset (S : TightSettingN F K z) {u v : F}
    (hu : u ∈ Zset K z) (hv : v ∈ Zset K z) :
    u ∈ Subgroup.centralizer ((memb K z v : Subgroup F) : Set F) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact S.mem_centralizer_of_commOrEq hu.1 (S.commOrEq_of_mem_Zset hv hu) hk

omit [Finite F] in
theorem TightSettingN.closure_Zset_le_centralizer (S : TightSettingN F K z) {v : F}
    (hv : v ∈ Zset K z) :
    Subgroup.closure (Zset K z) ≤ Subgroup.centralizer ((memb K z v : Subgroup F) : Set F) :=
  (Subgroup.closure_le _).mpr fun _ hu => S.mem_centralizer_memb_of_mem_Zset hu hv

omit [Finite F] in
theorem TightSettingN.Zset_commute (S : TightSettingN F K z) {u v : F} (hu : u ∈ Zset K z)
    (hv : v ∈ Zset K z) : u * v = v * u :=
  (Subgroup.mem_centralizer_iff.mp (S.mem_centralizer_memb_of_mem_Zset hu hv) v
    (S.mem_memb hv.1)).symm

omit [Finite F] in
theorem TightSettingN.isCommProd_of_mem_closure_Zset (S : TightSettingN F K z) {e : F}
    (he : e ∈ Subgroup.closure (Zset K z)) : IsCommProd z e :=
  ⟨Zset K z, fun _ hu => hu.1, fun _ ha _ hb => S.Zset_commute ha hb, he⟩

omit [Finite F] in
theorem TightSettingN.E_centralizes (S : TightSettingN F K z) {x w : F}
    (hx : x ∈ Subgroup.closure (Zset K z)) (hw : w ∈ Zset K z) : x * w = w * x := by
  have : Subgroup.closure (Zset K z) ≤ Subgroup.centralizer ({w} : Set F) := by
    rw [Subgroup.closure_le]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (S.Zset_commute hu hw).symm
  exact (Subgroup.mem_centralizer_iff.mp (this hx) w rfl).symm

omit [Finite F] in
theorem TightSettingN.E_comm (S : TightSettingN F K z) {x y : F}
    (hx : x ∈ Subgroup.closure (Zset K z)) (hy : y ∈ Subgroup.closure (Zset K z)) :
    x * y = y * x := by
  have : Subgroup.closure (Zset K z) ≤ Subgroup.centralizer ({x} : Set F) := by
    rw [Subgroup.closure_le]
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact S.E_centralizes hx hw
  exact Subgroup.mem_centralizer_iff.mp (this hy) x rfl

omit [Finite F] in
theorem TightSettingN.E_sq (S : TightSettingN F K z) {x : F}
    (hx : x ∈ Subgroup.closure (Zset K z)) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    have := orderOf_eq_two_of_mem_classOf S.tight hx.1
    have h2 := pow_orderOf_eq_one x
    rwa [this, pow_two] at h2
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc := S.E_comm hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy]; group
  | inv x hx ih =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ih]; simp

omit [Finite F] in
theorem TightSettingN.memb_le_centralizer_iff (S : TightSettingN F K z) {e : F}
    (he : e ∈ Subgroup.closure (Zset K z)) (he1 : e ≠ 1) {w : F} (hw : w ∈ classOf z) :
    memb K z w ≤ Subgroup.centralizer ({e} : Set F) ↔ w ∈ Zset K z := by
  constructor
  · intro h
    have hK : memb K z z ≤ Subgroup.centralizer ({e} : Set F) :=
      le_centralizer_singleton_of_mem_centralizer
        (S.closure_Zset_le_centralizer S.self_mem_Zset he)
    have := S.commOrEq_of_le_centralizer
      (orderOf_eq_prime (by rw [pow_two]; exact S.E_sq he) he1)
      (S.isCommProd_of_mem_closure_Zset he) (mem_classOf_self z) hw hK h
    rw [memb_self S.tight] at this
    exact ⟨hw, this⟩
  · intro hwZ
    exact le_centralizer_singleton_of_mem_centralizer (S.closure_Zset_le_centralizer hwZ he)

omit [Finite F] in
theorem TightSettingN.conj_mem_Zset (S : TightSettingN F K z) {e : F}
    (he : e ∈ Subgroup.closure (Zset K z)) (he1 : e ≠ 1) {c : F}
    (hc : c ∈ Subgroup.centralizer ({e} : Set F)) {w : F} (hw : w ∈ Zset K z) :
    c * w * c⁻¹ ∈ Zset K z := by
  have hcw : c * w * c⁻¹ ∈ classOf z := mem_classOf_conj hw.1 c
  have hwle := (S.memb_le_centralizer_iff he he1 hw.1).mpr hw
  rw [← S.memb_le_centralizer_iff he he1 hcw, memb_conj S.tight hw.1 c]
  rintro _ ⟨y, hy, rfl⟩
  have hy' : e * y = y * e := Subgroup.mem_centralizer_iff.mp (hwle hy) e rfl
  have hc' : e * c = c * e := Subgroup.mem_centralizer_iff.mp hc e rfl
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  show e * (c * y * c⁻¹) = c * y * c⁻¹ * e
  have hc'' : c⁻¹ * e = e * c⁻¹ := by
    calc c⁻¹ * e = c⁻¹ * e * c * c⁻¹ := by group
      _ = c⁻¹ * (e * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * e) * c⁻¹ := by rw [hc']
      _ = e * c⁻¹ := by group
  calc e * (c * y * c⁻¹) = (e * c) * y * c⁻¹ := by group
    _ = c * e * y * c⁻¹ := by rw [hc']
    _ = c * (e * y) * c⁻¹ := by group
    _ = c * (y * e) * c⁻¹ := by rw [hy']
    _ = c * y * (e * c⁻¹) := by group
    _ = c * y * (c⁻¹ * e) := by rw [hc'']
    _ = c * y * c⁻¹ * e := by group

omit [Finite F] in
theorem TightSettingN.centralizer_le_setNormalizer (S : TightSettingN F K z) {e : F}
    (he : e ∈ Subgroup.closure (Zset K z)) (he1 : e ≠ 1) :
    Subgroup.centralizer ({e} : Set F) ≤ Subgroup.normalizer (Zset K z) := by
  intro c hc
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  constructor
  · exact S.conj_mem_Zset he he1 hc
  · intro hn
    have hc' : c⁻¹ ∈ Subgroup.centralizer ({e} : Set F) := Subgroup.inv_mem _ hc
    have := S.conj_mem_Zset he he1 hc' hn
    simpa [mul_assoc] using this

theorem TightSettingN.mem_Zset_of_commute (S : TightSettingN F K z) {u : F} (hu : u ∈ classOf z)
    (hcomm : u * z = z * u) : u ∈ Zset K z := by
  have hz := S.tight.classical
  have hTL := S.tight.memb hu
  have hKz : memb K z z = K := memb_self S.tight
  have hunorm : u ∈ Subgroup.normalizer (K : Set F) := S.tight.tight (by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hcomm.symm)
  have hu2 : u * u = 1 := hTL.classical.mul_self
  obtain ⟨R, hRK, hR2, hR8, hRcomm⟩ := exists_two_subgroup_centralizing hz.witness hunorm hu2
  have hRC : R ≤ Subgroup.centralizer ({u} : Set F) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hRcomm r hr
  have hRN : R ≤ Subgroup.normalizer (memb K z u : Set F) := fun r hr => hTL.tight (hRC hr)
  have huniq : ∀ x ∈ R, orderOf x = 2 → x = z := fun x hx hx2 =>
    hz.eq_of_orderOf_eq_two (hRK hx) hx2
  have hzR : z ∈ R := by
    have hdvd : 2 ∣ Nat.card R := by
      obtain ⟨k, hk⟩ := hR2.exists_card_eq
      rw [hk] at hR8 ⊢
      have : k ≠ 0 := by
        rintro rfl
        simp at hR8
      exact dvd_pow_self 2 this
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have : (x : F) = z := huniq x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)
    rw [← this]
    exact x.2
  have htriv := oddQuotAut_conjOn_eq_one_of_card hTL.classical.witness hRN hR2 hzR huniq (by omega)
  have hzN : z ∈ Subgroup.normalizer (memb K z u : Set F) := hRN hzR
  have hL : memb K z u ≤ Subgroup.centralizer ({z} : Set F) := by
    have hzc := centralizes_of_oddQuotAut_eq_one hTL.classical.perfect
      (S.P1 _ u (S.isConjSubgroup_memb hu) hTL.classical) hzN htriv
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hzc k hk).symm
  have hK : memb K z z ≤ Subgroup.centralizer ({z} : Set F) := by
    rw [hKz]; exact hz.le_centralizer
  have := S.commOrEq_of_le_centralizer (orderOf_eq_two_of_mem_classOf S.tight (mem_classOf_self z))
    (isCommProd_of_mem_classOf (mem_classOf_self z)) (mem_classOf_self z) hu hK hL
  rw [hKz] at this
  exact ⟨hu, this⟩

end Clique

end CFSG.ClassicalInvolution.Hat2A7N
