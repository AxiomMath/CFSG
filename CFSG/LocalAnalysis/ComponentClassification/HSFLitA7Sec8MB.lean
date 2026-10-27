module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Twist
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Tower
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ComponentClassification.HSFLit.Sec8

@[expose] def mB : TwData 4 where
  qmulT :=
    64086703473722659906063414547407546821275210100914294696775666092954118009360 + 2 ^ 256 *
    (91331069496571062082413637914878861331952067979699504666630019730074294580820 + 2 ^ 256 *
    (2330922575911298785090663140898620990383977534483543249797693867280842930840 + 2 ^ 256 *
    (29575288598759700961440886508369935501060835413268753219652047504401019502300)))
  qinvT := 13753142893736129040
  actT :=
    93174097417875660688268507791454151307815279199902324172720061195076915966480 + 2 ^ 256 *
    (99932287442226494482229386224930055817241527191141490601105365918652578476560 + 2 ^ 256 *
    (31419258824119990419198055433595705494712942848320687435775306510216092987920 + 2 ^ 256 *
    (38177448848470824213158933867071610004139190839559853864160611233791755498000)))
  cocT :=
    14559151963706642893625244596345698227261367286990445508926355418298449920000 + 2 ^ 256 *
    (21797931722894586707502370957224717269949451775402635131729704932634356945152 + 2 ^ 256 *
    (482349680155951383671139967073101959600442770144910164869094806184912822304 + 2 ^ 256 *
    (7717594882495222126922518559500585210216352999771056719798902489685874979104)))

@[expose] def nfTabMB : ℕ :=
  94876056242969220981922775885296160533175114312311674183520787798845670035456 + 2 ^ 256 *
  (95784119493628531381774746027730931598736960688065333782801382563079345279490 + 2 ^ 256 *
  (96692402739131034768740002364293711132940884360148240498875326118021563679764 + 2 ^ 256 *
  (97600465993147174465527232832906593411739735650911477559841289807441338697238 + 2 ^ 256 *
  (40385661321294435583374668883795187658254266845776213499225005585938673833992 + 2 ^ 256 *
  (41293724571953745983226639026229958723816113221529873098505600350172349078026 + 2 ^ 256 *
  (42202007817456249370191895362792738258020036893612779814579543905114567478300 + 2 ^ 256 *
  (43110071071472389066979125831405620536818888184376016875545507594534342495774)))))))

theorem mB_valid : mB.Valid where
  qmul_assoc := by decide +kernel
  qone_mul := by decide +kernel
  qmul_one := by decide +kernel
  qinv_mul := by decide +kernel
  act_ex := by decide +kernel
  act_one := by decide +kernel
  act_mul := by decide +kernel
  coc_one_left := by decide +kernel
  coc_one_right := by decide +kernel
  coc_cocycle := by decide +kernel

abbrev MB : Type := mB.Carrier

instance : Group MB := TwData.group mB_valid

namespace MB

@[expose] def w₂ : MB := ⟨0, 1⟩
@[expose] def u : MB := ⟨0, 2⟩
@[expose] def w₁ : MB := ⟨1, 4⟩
@[expose] def v : MB := ⟨0, 8⟩
@[expose] def z : MB := ⟨1, 0⟩
@[expose] def y : MB := ⟨2, 0⟩
@[expose] def t : MB := ⟨4, 0⟩
@[expose] def k : MB := ⟨8, 0⟩

@[expose] def gens : List MB := [w₂, u, w₁, v, z, y, t, k]

@[expose] def nfBits (x : MB) : List Bool :=
  (List.range 8).map fun i => (tget nfTabMB 8 (16 * x.g.val + x.a.val)).testBit i

theorem nf_spec : ∀ x : MB, x = nfProd gens (nfBits x) := by decide +kernel

structure PcX {X : Type*} [Group X] (w₂' u' w₁' v' z' y' t' k' : X) : Prop where
  w₂_sq : w₂' * w₂' = y'
  w₂_u : w₂' * u' * w₂'⁻¹ = u' * w₁'
  w₂_w₁ : w₂' * w₁' * w₂'⁻¹ = w₁'
  w₂_v : w₂' * v' * w₂'⁻¹ = v' * y'
  w₂_z : w₂' * z' * w₂'⁻¹ = z'
  w₂_y : w₂' * y' * w₂'⁻¹ = y'
  w₂_t : w₂' * t' * w₂'⁻¹ = y' * t'
  w₂_k : w₂' * k' * w₂'⁻¹ = k'
  u_sq : u' * u' = 1
  u_w₁ : u' * w₁' * u'⁻¹ = w₁' * z'
  u_v : u' * v' * u'⁻¹ = v'
  u_z : u' * z' * u'⁻¹ = z'
  u_y : u' * y' * u'⁻¹ = z' * y'
  u_t : u' * t' * u'⁻¹ = t'
  u_k : u' * k' * u'⁻¹ = k'
  w₁_sq : w₁' * w₁' = z'
  w₁_v : w₁' * v' * w₁'⁻¹ = v' * z'
  w₁_z : w₁' * z' * w₁'⁻¹ = z'
  w₁_y : w₁' * y' * w₁'⁻¹ = y'
  w₁_t : w₁' * t' * w₁'⁻¹ = z' * t'
  w₁_k : w₁' * k' * w₁'⁻¹ = k'
  v_sq : v' * v' = 1
  v_z : v' * z' * v'⁻¹ = z'
  v_y : v' * y' * v'⁻¹ = y'
  v_t : v' * t' * v'⁻¹ = t' * k'
  v_k : v' * k' * v'⁻¹ = k'
  z_sq : z' * z' = 1
  z_y : z' * y' * z'⁻¹ = y'
  z_t : z' * t' * z'⁻¹ = t'
  z_k : z' * k' * z'⁻¹ = k'
  y_sq : y' * y' = 1
  y_t : y' * t' * y'⁻¹ = t'
  y_k : y' * k' * y'⁻¹ = k'
  t_sq : t' * t' = 1
  t_k : t' * k' * t'⁻¹ = k'
  k_sq : k' * k' = 1

theorem pcRel_of {X : Type*} [Group X] {w₂' u' w₁' v' z' y' t' k' : X}
    (h : PcX w₂' u' w₁' v' z' y' t' k') :
    PcRel [(w₂, w₂'), (u, u'), (w₁, w₁'), (v, v'), (z, z'), (y, y'), (t, t'), (k, k')] := by
  refine ⟨⟨[false, false, false, false, true, false, false], ?_,
    by simpa [nfProd] using h.w₂_sq⟩, ?_, ?_, ?_⟩
  · show w₂ * w₂ = nfProd [u, w₁, v, z, y, t, k] [false, false, false, false, true, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨[true, true, false, false, false, false, false], ?_, by simpa [nfProd] using h.w₂_u⟩
      show w₂ * u * w₂⁻¹ =
        nfProd [u, w₁, v, z, y, t, k] [true, true, false, false, false, false, false]
      decide +kernel
    · refine ⟨[false, true, false, false, false, false, false], ?_, by simpa [nfProd] using h.w₂_w₁⟩
      show w₂ * w₁ * w₂⁻¹ =
        nfProd [u, w₁, v, z, y, t, k] [false, true, false, false, false, false, false]
      decide +kernel
    · refine ⟨[false, false, true, false, true, false, false], ?_, by simpa [nfProd] using h.w₂_v⟩
      show w₂ * v * w₂⁻¹ =
        nfProd [u, w₁, v, z, y, t, k] [false, false, true, false, true, false, false]
      decide +kernel
    · refine ⟨[false, false, false, true, false, false, false], ?_, by simpa [nfProd] using h.w₂_z⟩
      show w₂ * z * w₂⁻¹ =
        nfProd [u, w₁, v, z, y, t, k] [false, false, false, true, false, false, false]
      decide +kernel
    · refine ⟨[false, false, false, false, true, false, false], ?_, by simpa [nfProd] using h.w₂_y⟩
      show w₂ * y * w₂⁻¹ =
        nfProd [u, w₁, v, z, y, t, k] [false, false, false, false, true, false, false]
      decide +kernel
    · refine ⟨[false, false, false, false, true, true, false], ?_, by simpa [nfProd] using h.w₂_t⟩
      show w₂ * t * w₂⁻¹ =
        nfProd [u, w₁, v, z, y, t, k] [false, false, false, false, true, true, false]
      decide +kernel
    · refine ⟨[false, false, false, false, false, false, true], ?_, by simpa [nfProd] using h.w₂_k⟩
      show w₂ * k * w₂⁻¹ =
        nfProd [u, w₁, v, z, y, t, k] [false, false, false, false, false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 7, w₂ ≠ nfProd [u, w₁, v, z, y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, false, false, false, false, false], ?_,
    by simpa [nfProd] using h.u_sq⟩, ?_, ?_, ?_⟩
  · show u * u = nfProd [w₁, v, z, y, t, k] [false, false, false, false, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨[true, false, true, false, false, false], ?_, by simpa [nfProd] using h.u_w₁⟩
      show u * w₁ * u⁻¹ = nfProd [w₁, v, z, y, t, k] [true, false, true, false, false, false]
      decide +kernel
    · refine ⟨[false, true, false, false, false, false], ?_, by simpa [nfProd] using h.u_v⟩
      show u * v * u⁻¹ = nfProd [w₁, v, z, y, t, k] [false, true, false, false, false, false]
      decide +kernel
    · refine ⟨[false, false, true, false, false, false], ?_, by simpa [nfProd] using h.u_z⟩
      show u * z * u⁻¹ = nfProd [w₁, v, z, y, t, k] [false, false, true, false, false, false]
      decide +kernel
    · refine ⟨[false, false, true, true, false, false], ?_, by simpa [nfProd] using h.u_y⟩
      show u * y * u⁻¹ = nfProd [w₁, v, z, y, t, k] [false, false, true, true, false, false]
      decide +kernel
    · refine ⟨[false, false, false, false, true, false], ?_, by simpa [nfProd] using h.u_t⟩
      show u * t * u⁻¹ = nfProd [w₁, v, z, y, t, k] [false, false, false, false, true, false]
      decide +kernel
    · refine ⟨[false, false, false, false, false, true], ?_, by simpa [nfProd] using h.u_k⟩
      show u * k * u⁻¹ = nfProd [w₁, v, z, y, t, k] [false, false, false, false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 6, u ≠ nfProd [w₁, v, z, y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, true, false, false, false], ?_, by simpa [nfProd] using h.w₁_sq⟩, ?_, ?_, ?_⟩
  · show w₁ * w₁ = nfProd [v, z, y, t, k] [false, true, false, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · refine ⟨[true, true, false, false, false], ?_, by simpa [nfProd] using h.w₁_v⟩
      show w₁ * v * w₁⁻¹ = nfProd [v, z, y, t, k] [true, true, false, false, false]
      decide +kernel
    · refine ⟨[false, true, false, false, false], ?_, by simpa [nfProd] using h.w₁_z⟩
      show w₁ * z * w₁⁻¹ = nfProd [v, z, y, t, k] [false, true, false, false, false]
      decide +kernel
    · refine ⟨[false, false, true, false, false], ?_, by simpa [nfProd] using h.w₁_y⟩
      show w₁ * y * w₁⁻¹ = nfProd [v, z, y, t, k] [false, false, true, false, false]
      decide +kernel
    · refine ⟨[false, true, false, true, false], ?_, by simpa [nfProd] using h.w₁_t⟩
      show w₁ * t * w₁⁻¹ = nfProd [v, z, y, t, k] [false, true, false, true, false]
      decide +kernel
    · refine ⟨[false, false, false, false, true], ?_, by simpa [nfProd] using h.w₁_k⟩
      show w₁ * k * w₁⁻¹ = nfProd [v, z, y, t, k] [false, false, false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 5, w₁ ≠ nfProd [v, z, y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, false, false, false], ?_, by simpa [nfProd] using h.v_sq⟩, ?_, ?_, ?_⟩
  · show v * v = nfProd [z, y, t, k] [false, false, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine ⟨[true, false, false, false], ?_, by simpa [nfProd] using h.v_z⟩
      show v * z * v⁻¹ = nfProd [z, y, t, k] [true, false, false, false]
      decide +kernel
    · refine ⟨[false, true, false, false], ?_, by simpa [nfProd] using h.v_y⟩
      show v * y * v⁻¹ = nfProd [z, y, t, k] [false, true, false, false]
      decide +kernel
    · refine ⟨[false, false, true, true], ?_, by simpa [nfProd] using h.v_t⟩
      show v * t * v⁻¹ = nfProd [z, y, t, k] [false, false, true, true]
      decide +kernel
    · refine ⟨[false, false, false, true], ?_, by simpa [nfProd] using h.v_k⟩
      show v * k * v⁻¹ = nfProd [z, y, t, k] [false, false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 4, v ≠ nfProd [z, y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, false, false], ?_, by simpa [nfProd] using h.z_sq⟩, ?_, ?_, ?_⟩
  · show z * z = nfProd [y, t, k] [false, false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨[true, false, false], ?_, by simpa [nfProd] using h.z_y⟩
      show z * y * z⁻¹ = nfProd [y, t, k] [true, false, false]
      decide +kernel
    · refine ⟨[false, true, false], ?_, by simpa [nfProd] using h.z_t⟩
      show z * t * z⁻¹ = nfProd [y, t, k] [false, true, false]
      decide +kernel
    · refine ⟨[false, false, true], ?_, by simpa [nfProd] using h.z_k⟩
      show z * k * z⁻¹ = nfProd [y, t, k] [false, false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 3, z ≠ nfProd [y, t, k] bs
    decide +kernel
  refine ⟨⟨[false, false], ?_, by simpa [nfProd] using h.y_sq⟩, ?_, ?_, ?_⟩
  · show y * y = nfProd [t, k] [false, false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨[true, false], ?_, by simpa [nfProd] using h.y_t⟩
      show y * t * y⁻¹ = nfProd [t, k] [true, false]
      decide +kernel
    · refine ⟨[false, true], ?_, by simpa [nfProd] using h.y_k⟩
      show y * k * y⁻¹ = nfProd [t, k] [false, true]
      decide +kernel
  · show ∀ bs ∈ allBits 2, y ≠ nfProd [t, k] bs
    decide +kernel
  refine ⟨⟨[false], ?_, by simpa [nfProd] using h.t_sq⟩, ?_, ?_, ?_⟩
  · show t * t = nfProd [k] [false]
    decide +kernel
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · refine ⟨[true], ?_, by simpa [nfProd] using h.t_k⟩
      show t * k * t⁻¹ = nfProd [k] [true]
      decide +kernel
  · show ∀ bs ∈ allBits 1, t ≠ nfProd [k] bs
    decide +kernel
  refine ⟨⟨[], ?_, by simpa [nfProd] using h.k_sq⟩, ?_, ?_, ?_⟩
  · show k * k = nfProd [] []
    decide +kernel
  · intro r hr
    simp at hr
  · show ∀ bs ∈ allBits 0, k ≠ nfProd [] bs
    decide +kernel
  trivial

theorem exists_hom {X : Type*} [Group X] {w₂' u' w₁' v' z' y' t' k' : X}
    (h : PcX w₂' u' w₁' v' z' y' t' k') :
    ∃ ι : MB →* X, ι w₂ = w₂' ∧ ι u = u' ∧ ι w₁ = w₁' ∧ ι v = v' ∧ ι z = z' ∧ ι y = y' ∧
      ι t = t' ∧ ι k = k' := by
  obtain ⟨F, hF, -⟩ := exists_hom_of_pcRel _ (pcRel_of h) (fun x =>
    ⟨nfBits x, by simpa [nfBits] using mem_allBits (nfBits x), nf_spec x⟩)
  exact ⟨F, hF (w₂, w₂') (by simp), hF (u, u') (by simp), hF (w₁, w₁') (by simp),
    hF (v, v') (by simp), hF (z, z') (by simp), hF (y, y') (by simp), hF (t, t') (by simp),
    hF (k, k') (by simp)⟩

theorem center_cases : ∀ x : MB, (∀ g ∈ gens, g * x = x * g) →
    x = 1 ∨ x = z ∨ x = k ∨ x = z * k := by
  decide +kernel

theorem card_eq : Nat.card MB = 2 ^ 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (TwData.Carrier.equiv mB), Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  norm_num

theorem isPGroup : IsPGroup 2 MB := IsPGroup.of_card card_eq

theorem injective_of {X : Type*} [Group X] (ι : MB →* X) (hz : ι z ≠ 1) (hk : ι k ≠ 1)
    (hzk : ι z * ι k ≠ 1) : Function.Injective ι := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent MB := isPGroup.isNilpotent
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨x, hxk, hxc⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  rcases center_cases x (fun g _ => Subgroup.mem_center_iff.mp hxc g) with h1 | h1 | h1 | h1
  · exact hx1' h1
  · rw [h1] at hxk; exact hz hxk
  · rw [h1] at hxk; exact hk hxk
  · rw [h1] at hxk
    have h2 : ι (z * k) = 1 := hxk
    rw [map_mul] at h2
    exact hzk h2

theorem range_le {X : Type*} [Group X] (ι : MB →* X) {H : Subgroup X}
    (h : ∀ g ∈ gens, ι g ∈ H) : ι.range ≤ H := by
  rintro _ ⟨x, rfl⟩
  rw [nf_spec x]
  exact map_mem_of_inSpan ι ⟨nfBits x, by simpa [nfBits, gens] using mem_allBits (nfBits x), rfl⟩ h

end MB

end CFSG.ComponentClassification.HSFLit.Sec8
